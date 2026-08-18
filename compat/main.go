package main

import (
	"bufio"
	"encoding/json"
	"fmt"
	"os"
	"strings"

	goexpr "github.com/expr-lang/expr"
)

func main() {
	file, err := os.Open("cases.tsv")
	if err != nil {
		panic(err)
	}
	defer file.Close()

	scanner := bufio.NewScanner(file)
	line := 0
	for scanner.Scan() {
		line++
		text := scanner.Text()
		if text == "" || strings.HasPrefix(text, "#") {
			continue
		}
		parts := strings.SplitN(text, "\t", 2)
		if len(parts) != 2 {
			panic(fmt.Sprintf("cases.tsv:%d: expected expression and result", line))
		}
		program, err := goexpr.Compile(parts[0])
		if err != nil {
			panic(fmt.Sprintf("cases.tsv:%d: %v", line, err))
		}
		result, err := goexpr.Run(program, nil)
		if err != nil {
			panic(fmt.Sprintf("cases.tsv:%d: %v", line, err))
		}
		actual, err := json.Marshal(result)
		if err != nil {
			panic(fmt.Sprintf("cases.tsv:%d: %v", line, err))
		}
		var expected any
		decoder := json.NewDecoder(strings.NewReader(parts[1]))
		decoder.UseNumber()
		if err := decoder.Decode(&expected); err != nil {
			panic(fmt.Sprintf("cases.tsv:%d: invalid expected JSON: %v", line, err))
		}
		want, err := json.Marshal(expected)
		if err != nil {
			panic(fmt.Sprintf("cases.tsv:%d: %v", line, err))
		}
		if string(actual) != string(want) {
			panic(fmt.Sprintf("cases.tsv:%d: got %s, want %s", line, actual, want))
		}
	}
	if err := scanner.Err(); err != nil {
		panic(err)
	}
	fmt.Printf("verified %d lines against Go expr v1.17.8\n", line)
}
