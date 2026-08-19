use crate::{bail, value::{DateTimeValue, TimezoneValue}, Environment, Error, Value};
use chrono::{DateTime, Datelike, Duration, FixedOffset, NaiveDate, NaiveDateTime, NaiveTime, Offset, TimeZone, Timelike, Utc};
use chrono_tz::{OffsetComponents, Tz};
use once_cell::sync::Lazy;
use regex::Regex;

const NANOS_PER_MICRO: i64 = 1_000;
const NANOS_PER_MILLI: i64 = 1_000_000;
const NANOS_PER_SECOND: i64 = 1_000_000_000;
const NANOS_PER_MINUTE: i64 = 60 * NANOS_PER_SECOND;
const NANOS_PER_HOUR: i64 = 60 * NANOS_PER_MINUTE;

static COMPACT_OFFSET: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"([+-])(\d{2})(\d{2})(\d{2})").expect("valid offset regex"));
static SECONDS_OFFSET: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"([+-])(\d{2}):(\d{2}):(\d{2})").expect("valid offset regex"));
static TRAILING_ZONE: Lazy<Regex> =
    Lazy::new(|| Regex::new(r"([A-Za-z]{3,5})\s*$").expect("valid zone-name regex"));

pub fn add_temporal_functions(env: &mut Environment) {
    env.add_function("now", |call| {
        if !call.args.is_empty() {
            bail!("now() takes no arguments");
        }
        Ok(Value::DateTime(DateTimeValue::zoned(Utc::now().with_timezone(&chrono_tz::UTC), chrono_tz::UTC)))
    });

    env.add_function("duration", |mut call| {
        if call.args.len() != 1 {
            bail!("duration() takes exactly one argument");
        }
        let Value::String(value) = call.args.pop().expect("length checked") else {
            bail!("duration() takes a string");
        };
        parse_duration(&value).map(Value::Duration)
    });

    env.add_function("timezone", |mut call| {
        if call.args.len() != 1 {
            bail!("timezone() takes exactly one argument");
        }
        let Value::String(value) = call.args.pop().expect("length checked") else {
            bail!("timezone() takes a string");
        };
        parse_timezone(&value).map(Value::Timezone)
    });

    env.add_function("date", |call| parse_date(call.args).map(Value::DateTime));
}

fn parse_timezone(value: &str) -> crate::Result<TimezoneValue> {
    if value == "Local" {
        TimezoneValue::local()
            .map_err(|error| Error::ExprError(format!("invalid local timezone: {error}")))
    } else {
        value
            .parse::<Tz>()
            .map(TimezoneValue::named)
            .map_err(|error| Error::ExprError(format!("invalid timezone {value}: {error}")))
    }
}

fn parse_duration(value: &str) -> crate::Result<i64> {
    if value == "0" {
        return Ok(0);
    }
    let (sign, value) = value
        .strip_prefix('-')
        .map_or_else(|| (1.0, value.strip_prefix('+').unwrap_or(value)), |value| (-1.0, value));
    if value.is_empty() {
        bail!("invalid duration");
    }

    let mut remaining = value;
    let mut total = 0.0_f64;
    while !remaining.is_empty() {
        let number_end = remaining
            .char_indices()
            .take_while(|(_, character)| character.is_ascii_digit() || *character == '.')
            .map(|(index, character)| index + character.len_utf8())
            .last()
            .unwrap_or(0);
        if number_end == 0 {
            bail!("invalid duration {value}");
        }
        let number = remaining[..number_end]
            .parse::<f64>()
            .map_err(|_| Error::ExprError(format!("invalid duration {value}")))?;
        remaining = &remaining[number_end..];
        let (unit, multiplier) = [
            ("ns", 1.0),
            ("us", NANOS_PER_MICRO as f64),
            ("µs", NANOS_PER_MICRO as f64),
            ("μs", NANOS_PER_MICRO as f64),
            ("ms", NANOS_PER_MILLI as f64),
            ("s", NANOS_PER_SECOND as f64),
            ("m", NANOS_PER_MINUTE as f64),
            ("h", NANOS_PER_HOUR as f64),
        ]
        .into_iter()
        .find(|(unit, _)| remaining.starts_with(unit))
        .ok_or_else(|| Error::ExprError(format!("invalid duration {value}")))?;
        total += number * multiplier;
        remaining = &remaining[unit.len()..];
    }

    let total = total * sign;
    if !total.is_finite() || total < i64::MIN as f64 || total > i64::MAX as f64 {
        bail!("duration out of range");
    }
    Ok(total.trunc() as i64)
}

fn parse_date(mut args: Vec<Value>) -> crate::Result<DateTimeValue> {
    if args.is_empty() || args.len() > 3 {
        bail!("date() takes one to three arguments");
    }
    let leading_timezone = if matches!(args.first(), Some(Value::Timezone(_))) {
        let Value::Timezone(timezone) = args.remove(0) else { unreachable!("checked") };
        Some(timezone)
    } else {
        None
    };
    let has_named_location = leading_timezone.is_some() || args.get(2).is_some();
    if args.is_empty() {
        bail!("date() requires a date string");
    }
    let Value::String(value) = &args[0] else {
        bail!("date() first argument must be a string");
    };
    let timezone = match args.get(2) {
        Some(Value::String(value)) => parse_timezone(value)?,
        Some(_) => bail!("date() timezone must be a string"),
        None => leading_timezone.unwrap_or_else(|| TimezoneValue::named(chrono_tz::UTC)),
    };

    if let Some(layout) = args.get(1) {
        let Value::String(layout) = layout else {
            bail!("date() format must be a string");
        };
        let mut parse_value = value.clone();
        if layout.contains("070000") {
            parse_value = COMPACT_OFFSET
                .replace_all(&parse_value, "$1$2:$3:$4")
                .into_owned();
        }
        if (layout.contains("Z070000") || layout.contains("Z07:00:00"))
            && parse_value.ends_with('Z')
        {
            parse_value.pop();
            parse_value.push_str("+00:00:00");
        } else if layout.contains("Z07:00") && parse_value.ends_with('Z') {
            parse_value.pop();
            parse_value.push_str("+00:00");
        } else if layout.contains("Z0700") && parse_value.ends_with('Z') {
            parse_value.pop();
            parse_value.push_str("+0000");
        } else if layout.contains("Z07") && parse_value.ends_with('Z') {
            parse_value.pop();
            parse_value.push_str("+00");
        }
        let exact_offset = SECONDS_OFFSET.captures(&parse_value).and_then(|captures| {
            let sign = if &captures[1] == "-" { -1 } else { 1 };
            let hours = captures[2].parse::<i32>().ok()?;
            let minutes = captures[3].parse::<i32>().ok()?;
            let seconds = captures[4].parse::<i32>().ok()?;
            FixedOffset::east_opt(sign * (hours * 3600 + minutes * 60 + seconds))
        });
        if exact_offset.is_some() {
            parse_value = SECONDS_OFFSET.replace(&parse_value, "$1$2:$3").into_owned();
        }
        if layout.contains("05,") {
            parse_value = parse_value.replacen(',', ".", 1);
        }
        let mut format = go_layout_to_chrono(layout);
        if !layout.contains("PM") && !layout.contains("pm") {
            // Chrono requires an AM/PM marker with `%I`; Go defaults a
            // standalone 12-hour clock token to AM while parsing.
            format = format.replace("%-I", "%-H").replace("%I", "%H");
        }
        let mut parsed = parse_in_timezone(&parse_value, &format, timezone)?;
        if layout.contains("MST") && !has_named_location {
            let zone_name = TRAILING_ZONE
                .captures(value)
                .map(|captures| captures[1].to_string());
            if let Some(zone_name) = zone_name {
                parsed = parsed.with_zone_name(zone_name);
            }
        }
        if let Some(offset) = exact_offset {
            return offset
                .from_local_datetime(&parsed.naive_local())
                .single()
                .map(DateTimeValue::fixed)
                .ok_or_else(|| Error::ExprError("invalid date offset".to_string()));
        }
        return Ok(parsed);
    }

    if let Ok(value) = DateTime::parse_from_rfc3339(value) {
        return Ok(if value.offset().local_minus_utc() == 0 {
            DateTimeValue::zoned(value.with_timezone(&chrono_tz::UTC), chrono_tz::UTC)
        } else {
            DateTimeValue::fixed(value)
        });
    }
    for format in [
        "%Y-%m-%d",
        "%H:%M:%S",
        "%Y-%m-%d %H:%M:%S",
        "%d %b %y %H:%M %Z",
        "%A, %d-%b-%y %H:%M:%S %Z",
        "%a, %d %b %Y %H:%M:%S %Z",
    ] {
        if let Ok(value) = parse_in_timezone(value, format, timezone) {
            return Ok(value);
        }
    }
    bail!("invalid date {value}")
}

fn parse_in_timezone(
    value: &str,
    format: &str,
    timezone: TimezoneValue,
) -> crate::Result<DateTimeValue> {
    if format.contains("%z")
        || format.contains("%:z")
        || format.contains("%::z")
        || format.contains("%#z")
    {
        let parsed = DateTime::parse_from_str(value, format)
            .map_err(|error| Error::ExprError(error.to_string()))?;
        return Ok(if parsed.offset().local_minus_utc() == 0 {
            DateTimeValue::zoned(parsed.with_timezone(&chrono_tz::UTC), chrono_tz::UTC)
        } else {
            DateTimeValue::fixed(parsed)
        });
    }
    let naive = if let Ok(value) = NaiveDateTime::parse_from_str(value, format) {
        value
    } else if let Ok(value) = NaiveDate::parse_from_str(value, format) {
        value.and_hms_opt(0, 0, 0).expect("valid time")
    } else if let Ok(value) = NaiveTime::parse_from_str(value, format) {
        NaiveDate::from_ymd_opt(0, 1, 1)
            .expect("valid date")
            .and_time(value)
    } else {
        bail!("invalid date {value}");
    };
    timezone
        .timezone()
        .from_local_datetime(&naive)
        .earliest()
        .map(|value| DateTimeValue::zoned(value, timezone))
        .ok_or_else(|| Error::ExprError(format!("invalid local date {value}")))
}

fn go_layout_to_chrono(layout: &str) -> String {
    let replacements = [
        ("January", "%B"),
        ("Monday", "%A"),
        ("2006", "%Y"),
        ("Z07:00:00", "%:z"),
        ("-07:00:00", "%:z"),
        ("Z070000", "%:z"),
        ("-070000", "%:z"),
        ("Z0700", "%#z"),
        ("-0700", "%z"),
        ("Z07:00", "%:z"),
        ("-07:00", "%:z"),
        ("Z07", "%#z"),
        ("-07", "%#z"),
        ("__2", "%_j"),
        ("002", "%j"),
        ("Jan", "%b"),
        ("Mon", "%a"),
        ("MST", "%Z"),
        ("PM", "%p"),
        ("pm", "%P"),
        ("06", "%y"),
        ("01", "%m"),
        ("02", "%d"),
        ("15", "%H"),
        ("03", "%I"),
        ("04", "%M"),
        ("05", "%S"),
        ("_2", "%e"),
        ("1", "%-m"),
        ("2", "%-d"),
        ("3", "%-I"),
        ("4", "%-M"),
        ("5", "%-S"),
    ];
    let mut output = String::new();
    let mut remaining = layout;
    while !remaining.is_empty() {
        if output.ends_with("%S") || output.ends_with("%-S") {
            if let Some((separator, digits)) = fractional_layout(remaining) {
                output.push_str("%.f");
                remaining = &remaining[separator.len_utf8() + digits..];
                continue;
            }
        }
        if let Some((token, replacement)) = replacements
            .iter()
            .find(|(token, _)| remaining.starts_with(token))
        {
            output.push_str(replacement);
            remaining = &remaining[token.len()..];
        } else {
            let character = remaining.chars().next().expect("not empty");
            if character == '%' {
                output.push_str("%%");
            } else {
                output.push(character);
            }
            remaining = &remaining[character.len_utf8()..];
        }
    }
    output
}

fn format_go_layout(value: &DateTimeValue, layout: &str) -> String {
    let mut output = String::new();
    let mut chrono_layout = String::new();
    let mut remaining = layout;
    while !remaining.is_empty() {
        let converted_layout = go_layout_to_chrono(&chrono_layout);
        if converted_layout.ends_with("%S") || converted_layout.ends_with("%-S") {
            if let Some((separator, digits)) = fractional_layout(remaining) {
                output.push_str(&value.format(&go_layout_to_chrono(&chrono_layout)).to_string());
                chrono_layout.clear();
                let nanos = format!("{:09}", value.nanosecond());
                let pattern = &remaining[separator.len_utf8()..separator.len_utf8() + digits];
                let mut fraction = nanos[..digits].to_string();
                if pattern.starts_with('9') {
                    while fraction.ends_with('0') {
                        fraction.pop();
                    }
                }
                if !fraction.is_empty() || pattern.starts_with('0') {
                    output.push(separator);
                    output.push_str(&fraction);
                }
                remaining = &remaining[separator.len_utf8() + digits..];
                continue;
            }
        }
        let special = [
            "Z07:00:00", "-07:00:00", "Z070000", "-070000", "Z07:00", "-07:00",
            "Z0700", "-0700", "Z07", "-07", "MST",
        ]
            .into_iter()
            .find(|token| remaining.starts_with(token));
        if let Some(token) = special {
            output.push_str(&value.format(&go_layout_to_chrono(&chrono_layout)).to_string());
            chrono_layout.clear();
            match token {
                "MST" => output.push_str(&value.zone_name()),
                token if token.starts_with('Z') && value.offset().local_minus_utc() == 0 => {
                    output.push('Z')
                }
                "Z07:00:00" | "-07:00:00" => output.push_str(&format_offset(value, true, true)),
                "Z070000" | "-070000" => output.push_str(&format_offset(value, false, true)),
                "Z07:00" | "-07:00" => output.push_str(&format_offset(value, true, false)),
                "Z0700" | "-0700" => output.push_str(&format_offset(value, false, false)),
                "Z07" | "-07" => {
                    let offset = value.offset().local_minus_utc();
                    output.push_str(&format!("{}{:02}", if offset < 0 { '-' } else { '+' }, offset.unsigned_abs() / 3600));
                }
                _ => unreachable!("known layout token"),
            }
            remaining = &remaining[token.len()..];
        } else {
            let character = remaining.chars().next().expect("not empty");
            chrono_layout.push(character);
            remaining = &remaining[character.len_utf8()..];
        }
    }
    output.push_str(&value.format(&go_layout_to_chrono(&chrono_layout)).to_string());
    output
}

fn fractional_layout(layout: &str) -> Option<(char, usize)> {
    let separator = layout.chars().next()?;
    if separator != '.' && separator != ',' {
        return None;
    }
    let digits = layout[separator.len_utf8()..]
        .chars()
        .take_while(|digit| *digit == '0' || *digit == '9')
        .collect::<String>();
    if digits.is_empty()
        || digits.len() > 9
        || (!digits.chars().all(|digit| digit == '0')
            && !digits.chars().all(|digit| digit == '9'))
    {
        None
    } else {
        Some((separator, digits.len()))
    }
}

fn format_offset(value: &DateTimeValue, colon: bool, seconds: bool) -> String {
    let offset = value.offset().local_minus_utc();
    let absolute = offset.unsigned_abs();
    let sign = if offset < 0 { '-' } else { '+' };
    let hours = absolute / 3600;
    let minutes = absolute / 60 % 60;
    let seconds_value = absolute % 60;
    match (colon, seconds) {
        (true, true) => format!("{sign}{hours:02}:{minutes:02}:{seconds_value:02}"),
        (false, true) => format!("{sign}{hours:02}{minutes:02}{seconds_value:02}"),
        (true, false) => format!("{sign}{hours:02}:{minutes:02}"),
        (false, false) => format!("{sign}{hours:02}{minutes:02}"),
    }
}

pub(crate) fn eval_method(receiver: Value, method: &str, args: Vec<Value>) -> crate::Result<Value> {
    match (receiver, method) {
        (Value::Duration(value), "Abs") => no_args(
            method,
            args,
            Value::Duration(if value == i64::MIN { i64::MAX } else { value.abs() }),
        ),
        (Value::Duration(value), "Round") => {
            let unit = one_duration_arg(method, args)?;
            Ok(Value::Duration(round_duration(value, unit)))
        }
        (Value::Duration(value), "Truncate") => {
            let unit = one_duration_arg(method, args)?;
            Ok(Value::Duration(truncate_duration(value, unit)))
        }
        (Value::Duration(value), "Hours") => no_args(method, args, Value::Float(value as f64 / NANOS_PER_HOUR as f64)),
        (Value::Duration(value), "Minutes") => no_args(method, args, Value::Float(value as f64 / NANOS_PER_MINUTE as f64)),
        (Value::Duration(value), "Seconds") => no_args(method, args, Value::Float(value as f64 / NANOS_PER_SECOND as f64)),
        (Value::Duration(value), "Milliseconds") => no_args(method, args, Value::Integer(value / NANOS_PER_MILLI)),
        (Value::Duration(value), "Microseconds") => no_args(method, args, Value::Integer(value / NANOS_PER_MICRO)),
        (Value::Duration(value), "Nanoseconds") => no_args(method, args, Value::Integer(value)),
        (Value::Duration(value), "String") => no_args(method, args, Value::String(format_duration(value))),
        (Value::DateTime(value), "Year") => no_args(method, args, Value::Integer(value.year().into())),
        (Value::DateTime(value), "Month") => no_args(method, args, Value::Month(value.month())),
        (Value::DateTime(value), "Day") => no_args(method, args, Value::Integer(value.day().into())),
        (Value::DateTime(value), "Hour") => no_args(method, args, Value::Integer(value.hour().into())),
        (Value::DateTime(value), "Minute") => no_args(method, args, Value::Integer(value.minute().into())),
        (Value::DateTime(value), "Second") => no_args(method, args, Value::Integer(value.second().into())),
        (Value::DateTime(value), "Nanosecond") => no_args(method, args, Value::Integer(value.nanosecond().into())),
        (Value::DateTime(value), "Weekday") => no_args(method, args, Value::Weekday(value.weekday().num_days_from_sunday())),
        (Value::DateTime(value), "YearDay") => no_args(method, args, Value::Integer(value.ordinal().into())),
        (Value::DateTime(value), "Unix") => no_args(method, args, Value::Integer(value.timestamp())),
        (Value::DateTime(value), "UnixMilli") => no_args(method, args, Value::Integer(value.timestamp_millis())),
        (Value::DateTime(value), "UnixMicro") => no_args(method, args, Value::Integer(value.timestamp_micros())),
        (Value::DateTime(value), "UnixNano") => no_args(method, args, Value::Integer(value.timestamp_nanos_opt().unwrap_or_default())),
        (Value::DateTime(value), "String") => no_args(method, args, Value::String(format_datetime(&value))),
        (Value::DateTime(value), "Add") => {
            let duration = one_duration_arg(method, args)?;
            value
                .checked_add_signed(Duration::nanoseconds(duration))
                .map(Value::DateTime)
                .ok_or_else(|| Error::ExprError("date out of range".to_string()))
        }
        (Value::DateTime(value), "AddDate") => {
            let [years, months, days] = three_integer_args(method, args)?;
            add_date(value, years, months, days).map(Value::DateTime)
        }
        (Value::DateTime(value), "After") => {
            let other = one_datetime_arg(method, args)?;
            Ok(Value::Bool(value > other))
        }
        (Value::DateTime(value), "Before") => {
            let other = one_datetime_arg(method, args)?;
            Ok(Value::Bool(value < other))
        }
        (Value::DateTime(value), "Compare") => {
            let other = one_datetime_arg(method, args)?;
            Ok(Value::Integer(value.cmp(&other) as i64))
        }
        (Value::DateTime(value), "Equal") => {
            let other = one_datetime_arg(method, args)?;
            Ok(Value::Bool(value == other))
        }
        (Value::DateTime(value), "IsDST") => {
            let is_dst = value.timezone().is_some_and(|timezone| {
                timezone.timezone()
                    .offset_from_utc_datetime(&value.naive_utc())
                    .dst_offset()
                    != Duration::zero()
            });
            no_args(method, args, Value::Bool(is_dst))
        }
        (Value::DateTime(value), "IsZero") => no_args(
            method,
            args,
            Value::Bool(
                value.naive_utc()
                    == NaiveDate::from_ymd_opt(1, 1, 1)
                        .expect("valid zero date")
                        .and_time(NaiveTime::MIN),
            ),
        ),
        (Value::DateTime(value), "Location") => {
            let timezone = value.timezone().or_else(|| {
                (value.offset().local_minus_utc() == 0)
                    .then_some(TimezoneValue::named(chrono_tz::UTC))
            });
            let timezone = timezone.ok_or_else(|| {
                Error::ExprError("fixed-offset date has no named timezone".to_string())
            })?;
            no_args(method, args, Value::Timezone(timezone))
        }
        (Value::DateTime(value), "UTC") => no_args(
            method,
            args,
            Value::DateTime(value.with_timezone(TimezoneValue::named(chrono_tz::UTC))),
        ),
        (Value::DateTime(value), "Local") => {
            let timezone = TimezoneValue::local()
                .map_err(|error| Error::ExprError(format!("invalid local timezone: {error}")))?;
            no_args(method, args, Value::DateTime(value.with_timezone(timezone)))
        }
        (Value::DateTime(value), "Round") => {
            let unit = one_duration_arg(method, args)?;
            round_datetime(value, unit, true).map(Value::DateTime)
        }
        (Value::DateTime(value), "Sub") => {
            let other = one_datetime_arg(method, args)?;
            (value - other)
                .num_nanoseconds()
                .map(Value::Duration)
                .ok_or_else(|| Error::ExprError("duration out of range".to_string()))
        }
        (Value::DateTime(value), "Truncate") => {
            let unit = one_duration_arg(method, args)?;
            round_datetime(value, unit, false).map(Value::DateTime)
        }
        (Value::DateTime(value), "In") => {
            if args.len() != 1 {
                bail!("In() takes exactly one argument");
            }
            let Value::Timezone(timezone) = args.into_iter().next().expect("length checked") else {
                bail!("In() takes a timezone");
            };
            Ok(Value::DateTime(value.with_timezone(timezone)))
        }
        (Value::DateTime(value), "Format") => {
            if args.len() != 1 {
                bail!("Format() takes exactly one argument");
            }
            let Value::String(layout) = args.into_iter().next().expect("length checked") else {
                bail!("Format() takes a string");
            };
            Ok(Value::String(format_go_layout(&value, &layout)))
        }
        (Value::Timezone(value), "String") => no_args(method, args, Value::String(value.to_string())),
        (Value::Month(value), "String") => no_args(method, args, Value::String(month_name(value).to_string())),
        (Value::Weekday(value), "String") => no_args(method, args, Value::String(weekday_name(value).to_string())),
        (receiver, method) => bail!("type {receiver:?} has no method {method}()"),
    }
}

fn one_duration_arg(method: &str, mut args: Vec<Value>) -> crate::Result<i64> {
    if args.len() != 1 {
        bail!("{method}() takes exactly one argument");
    }
    let Value::Duration(value) = args.pop().expect("length checked") else {
        bail!("{method}() takes a duration");
    };
    Ok(value)
}

fn one_datetime_arg(method: &str, mut args: Vec<Value>) -> crate::Result<DateTimeValue> {
    if args.len() != 1 {
        bail!("{method}() takes exactly one argument");
    }
    let Value::DateTime(value) = args.pop().expect("length checked") else {
        bail!("{method}() takes a date");
    };
    Ok(value)
}

fn three_integer_args(method: &str, args: Vec<Value>) -> crate::Result<[i64; 3]> {
    if args.len() != 3 {
        bail!("{method}() takes exactly three arguments");
    }
    let values = args
        .into_iter()
        .map(|value| match value {
            Value::Integer(value) => Ok(value),
            _ => bail!("{method}() arguments must be integers"),
        })
        .collect::<crate::Result<Vec<_>>>()?;
    Ok(values.try_into().expect("length checked"))
}

fn add_date(value: DateTimeValue, years: i64, months: i64, days: i64) -> crate::Result<DateTimeValue> {
    let original_year = value.year();
    let original_month = value.month0();
    let month_index = i64::from(original_year)
        .checked_mul(12)
        .and_then(|value| value.checked_add(i64::from(original_month)))
        .and_then(|value| value.checked_add(years.checked_mul(12)?))
        .and_then(|value| value.checked_add(months))
        .ok_or_else(|| Error::ExprError("date out of range".to_string()))?;
    let year = i32::try_from(month_index.div_euclid(12))
        .map_err(|_| Error::ExprError("date out of range".to_string()))?;
    let month = u32::try_from(month_index.rem_euclid(12) + 1).expect("month in range");
    let day_offset = i64::from(value.day() - 1)
        .checked_add(days)
        .ok_or_else(|| Error::ExprError("date out of range".to_string()))?;
    let naive = NaiveDate::from_ymd_opt(year, month, 1)
        .and_then(|date| date.and_time(value.time()).checked_add_signed(Duration::days(day_offset)))
        .ok_or_else(|| Error::ExprError("date out of range".to_string()))?;
    if let Some(timezone) = value.timezone() {
        timezone
            .timezone()
            .from_local_datetime(&naive)
            .earliest()
            .map(|value| DateTimeValue::zoned(value, timezone))
            .ok_or_else(|| Error::ExprError("invalid local date".to_string()))
    } else {
        value
            .offset()
            .fix()
            .from_local_datetime(&naive)
            .single()
            .map(DateTimeValue::fixed)
            .ok_or_else(|| Error::ExprError("invalid local date".to_string()))
    }
}

fn truncate_duration(value: i64, unit: i64) -> i64 {
    if unit <= 0 {
        value
    } else {
        value / unit * unit
    }
}

fn round_duration(value: i64, unit: i64) -> i64 {
    if unit <= 0 {
        return value;
    }
    let remainder = value % unit;
    let truncated = value - remainder;
    if remainder.unsigned_abs() < (unit as u64).div_ceil(2) {
        truncated
    } else if value < 0 {
        truncated.saturating_sub(unit)
    } else {
        truncated.saturating_add(unit)
    }
}

fn round_datetime(value: DateTimeValue, unit: i64, round: bool) -> crate::Result<DateTimeValue> {
    if unit <= 0 {
        return Ok(value);
    }
    let utc = value.naive_utc();
    let zero = NaiveDate::from_ymd_opt(1, 1, 1).expect("valid zero date");
    let days = utc.date().signed_duration_since(zero).num_days() as i128;
    let absolute = days * i128::from(86_400 * NANOS_PER_SECOND)
        + i128::from(utc.time().num_seconds_from_midnight()) * i128::from(NANOS_PER_SECOND)
        + i128::from(utc.nanosecond());
    let unit = i128::from(unit);
    let remainder = absolute.rem_euclid(unit);
    let delta = if round && remainder * 2 >= unit {
        unit - remainder
    } else {
        -remainder
    };
    let delta = i64::try_from(delta)
        .map_err(|_| Error::ExprError("date out of range".to_string()))?;
    value
        .checked_add_signed(Duration::nanoseconds(delta))
        .ok_or_else(|| Error::ExprError("date out of range".to_string()))
}

pub(crate) fn date_to_rfc3339(value: &DateTimeValue) -> String {
    format_go_layout(value, "2006-01-02T15:04:05.999999999Z07:00")
}

fn no_args(method: &str, args: Vec<Value>, result: Value) -> crate::Result<Value> {
    if !args.is_empty() {
        bail!("{method}() takes no arguments");
    }
    Ok(result)
}

pub(crate) fn month_name(month: u32) -> &'static str {
    ["", "January", "February", "March", "April", "May", "June", "July", "August", "September", "October", "November", "December"]
        .get(month as usize)
        .copied()
        .unwrap_or("")
}

pub(crate) fn weekday_name(day: u32) -> &'static str {
    ["Sunday", "Monday", "Tuesday", "Wednesday", "Thursday", "Friday", "Saturday"]
        .get(day as usize)
        .copied()
        .unwrap_or("")
}

pub(crate) fn format_duration(value: i64) -> String {
    if value == 0 {
        return "0s".to_string();
    }
    let negative = value < 0;
    let mut value = value.unsigned_abs();
    let hours = value / NANOS_PER_HOUR as u64;
    value %= NANOS_PER_HOUR as u64;
    let minutes = value / NANOS_PER_MINUTE as u64;
    value %= NANOS_PER_MINUTE as u64;
    let seconds = value / NANOS_PER_SECOND as u64;
    let nanos = value % NANOS_PER_SECOND as u64;
    let mut output = if negative { "-".to_string() } else { String::new() };
    if hours == 0 && minutes == 0 && seconds == 0 {
        if nanos >= NANOS_PER_MILLI as u64 {
            output.push_str(&format_subsecond(nanos, NANOS_PER_MILLI as u64, 6, "ms"));
        } else if nanos >= NANOS_PER_MICRO as u64 {
            output.push_str(&format_subsecond(nanos, NANOS_PER_MICRO as u64, 3, "µs"));
        } else {
            output.push_str(&format!("{nanos}ns"));
        }
        return output;
    }
    if hours > 0 {
        output.push_str(&format!("{hours}h"));
    }
    if minutes > 0 || hours > 0 {
        output.push_str(&format!("{minutes}m"));
    }
    if nanos == 0 {
        output.push_str(&format!("{seconds}s"));
    } else {
        let fraction = format!("{nanos:09}").trim_end_matches('0').to_string();
        output.push_str(&format!("{seconds}.{fraction}s"));
    }
    output
}

fn format_subsecond(nanos: u64, divisor: u64, precision: usize, suffix: &str) -> String {
    let whole = nanos / divisor;
    let remainder = nanos % divisor;
    if remainder == 0 {
        return format!("{whole}{suffix}");
    }
    let fraction = format!("{remainder:0precision$}")
        .trim_end_matches('0')
        .to_string();
    format!("{whole}.{fraction}{suffix}")
}

pub(crate) fn format_datetime(value: &DateTimeValue) -> String {
    let mut output = value.format("%Y-%m-%d %H:%M:%S").to_string();
    if value.nanosecond() != 0 {
        output.push('.');
        output.push_str(format!("{:09}", value.nanosecond()).trim_end_matches('0'));
    }
    output.push(' ');
    output.push_str(&value.format("%z").to_string());
    output.push(' ');
    output.push_str(&value.zone_name());
    output
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn local_location_retains_dst_rules() {
        let timezone = TimezoneValue::local_with_timezone(chrono_tz::America::New_York);
        let value = timezone
            .timezone()
            .with_ymd_and_hms(2023, 8, 14, 12, 0, 0)
            .single()
            .expect("valid local date");
        let value = DateTimeValue::zoned(value, timezone);

        assert_eq!(
            eval_method(Value::DateTime(value.clone()), "Location", vec![]).unwrap(),
            Value::Timezone(timezone)
        );
        assert_eq!(
            eval_method(Value::DateTime(value), "IsDST", vec![]).unwrap(),
            Value::Bool(true)
        );
    }
}
