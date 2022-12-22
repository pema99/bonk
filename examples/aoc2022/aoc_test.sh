#!/bin/sh
> out.txt
echo "Day 1:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day1/day1.bonk   && bun out.js >> out.txt
echo "Day 2:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day2/day2.bonk   && bun out.js >> out.txt
echo "Day 3:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day3/day3.bonk   && bun out.js >> out.txt
echo "Day 4:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day4/day4.bonk   && bun out.js >> out.txt
echo "Day 5:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day5/day5.bonk   && bun out.js >> out.txt
echo "Day 6:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day6/day6.bonk   && bun out.js >> out.txt
echo "Day 7:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day7/day7.bonk   && bun out.js >> out.txt
echo "Day 8:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day8/day8.bonk   && bun out.js >> out.txt
echo "Day 9:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day9/day9.bonk   && bun out.js >> out.txt
echo "Day 10:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day10/day10.bonk && bun out.js >> out.txt
echo "Day 11:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day11/day11.bonk && bun out.js >> out.txt
echo "Day 12:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day12/day12.bonk && bun out.js >> out.txt
echo "Day 13:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day13/day13.bonk && bun out.js >> out.txt
echo "Day 14:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day14/day14.bonk && bun out.js >> out.txt
echo "Day 18:" >> out.txt
dotnet run compile lib/bonk/prelude_js.bonk examples/aoc2022/day18/day18.bonk && bun out.js >> out.txt