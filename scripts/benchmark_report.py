#!/usr/bin/env python3
import json
import sys

def report(file_path):
    print(f"Reading {file_path}")
    with open(file_path) as user_file:
        file_contents = user_file.read()
    parsed_json = json.loads(file_contents)
    print("Benchmark results:")
    for key, value in parsed_json.items():
        average = sum(value) / len(value)
        std_dev = (sum([(x - average) ** 2 for x in value]) / len(value)) ** 0.5
        print(f" * {average:.1f}\t± {std_dev:.1f}\tseconds for {key}")

if __name__ == "__main__":
    if len(sys.argv) < 2:
        print("Usage: python3 benchmark_report.py <file_path>")
        sys.exit(1)
    report(sys.argv[1])
