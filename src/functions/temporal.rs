use crate::{bail, value::DateTimeValue, Environment, Error, Value};
use chrono::{DateTime, Datelike, NaiveDate, NaiveDateTime, NaiveTime, SecondsFormat, TimeZone, Timelike, Utc};
use chrono_tz::Tz;

const NANOS_PER_MICRO: i64 = 1_000;
const NANOS_PER_MILLI: i64 = 1_000_000;
const NANOS_PER_SECOND: i64 = 1_000_000_000;
const NANOS_PER_MINUTE: i64 = 60 * NANOS_PER_SECOND;
const NANOS_PER_HOUR: i64 = 60 * NANOS_PER_MINUTE;

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
        value
            .parse::<Tz>()
            .map(Value::Timezone)
            .map_err(|error| Error::ExprError(format!("invalid timezone {value}: {error}")))
    });

    env.add_function("date", |call| parse_date(call.args).map(Value::DateTime));
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

fn parse_date(args: Vec<Value>) -> crate::Result<DateTimeValue> {
    if args.is_empty() || args.len() > 3 {
        bail!("date() takes one to three arguments");
    }
    let Value::String(value) = &args[0] else {
        bail!("date() first argument must be a string");
    };
    let timezone = match args.get(2) {
        Some(Value::String(value)) => value
            .parse::<Tz>()
            .map_err(|error| Error::ExprError(format!("invalid timezone {value}: {error}")))?,
        Some(_) => bail!("date() timezone must be a string"),
        None => chrono_tz::UTC,
    };

    if let Some(layout) = args.get(1) {
        let Value::String(layout) = layout else {
            bail!("date() format must be a string");
        };
        let mut format = go_layout_to_chrono(layout);
        if !layout.contains("PM") && !layout.contains("pm") {
            // Chrono requires an AM/PM marker with `%I`; Go defaults a
            // standalone 12-hour clock token to AM while parsing.
            format = format.replace("%-I", "%-H").replace("%I", "%H");
        }
        return parse_in_timezone(value, &format, timezone);
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

fn parse_in_timezone(value: &str, format: &str, timezone: Tz) -> crate::Result<DateTimeValue> {
    if format.contains("%z") || format.contains("%:z") || format.contains("%#z") {
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
        ("Z0700", "%#z"),
        ("-0700", "%z"),
        ("Z07:00", "%:z"),
        ("-07:00", "%:z"),
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
        let special = ["Z07:00", "Z0700", "MST"]
            .into_iter()
            .find(|token| remaining.starts_with(token));
        if let Some(token) = special {
            output.push_str(&value.format(&go_layout_to_chrono(&chrono_layout)).to_string());
            chrono_layout.clear();
            match token {
                "MST" => output.push_str(&value.zone_name()),
                "Z07:00" if value.offset().local_minus_utc() == 0 => output.push('Z'),
                "Z07:00" => output.push_str(&value.format("%:z").to_string()),
                "Z0700" if value.offset().local_minus_utc() == 0 => output.push('Z'),
                "Z0700" => output.push_str(&value.format("%z").to_string()),
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

pub(crate) fn eval_method(receiver: Value, method: &str, args: Vec<Value>) -> crate::Result<Value> {
    match (receiver, method) {
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

pub(crate) fn date_to_rfc3339(value: &DateTimeValue) -> String {
    value.to_rfc3339_opts(SecondsFormat::AutoSi, true)
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

fn format_datetime(value: &DateTimeValue) -> String {
    let mut output = value.format("%Y-%m-%d %H:%M:%S %z").to_string();
    output.push(' ');
    output.push_str(&value.zone_name());
    output
}
