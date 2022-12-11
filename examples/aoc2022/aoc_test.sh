#!/bin/sh
> out.txt
dotnet run compile examples/aoc2022/day1/day1.bonk && bun out.js >> out.txt
dotnet run compile examples/aoc2022/day2/day2.bonk && bun out.js >> out.txt
dotnet run compile examples/aoc2022/day3/day3.bonk && bun out.js >> out.txt
dotnet run compile examples/aoc2022/day4/day4.bonk && bun out.js >> out.txt
dotnet run compile examples/aoc2022/day5/day5.bonk && bun out.js >> out.txt
dotnet run compile examples/aoc2022/day6/day6.bonk && bun out.js >> out.txt
dotnet run compile examples/aoc2022/day7/day7.bonk && bun out.js >> out.txt
dotnet run compile examples/aoc2022/day8/day8.bonk && bun out.js >> out.txt
dotnet run compile examples/aoc2022/day9/day9.bonk && bun out.js >> out.txt
dotnet run compile examples/aoc2022/day10/day10.bonk && bun out.js >> out.txt