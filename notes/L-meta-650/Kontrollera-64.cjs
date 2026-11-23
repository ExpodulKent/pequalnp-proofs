// Kör med: node Kontrollera-64.cjs
// Varje rad hör till en punkt. Linjerna numreras från 0 till 12.
const assert = require('node:assert/strict');
const linesAtPoint = [[0,1,3,9],
  [0,2,8,12],
  [1,7,11,12],
  [0,6,10,11],
  [5,9,10,12],
  [4,8,9,11],
  [3,7,8,10],
  [2,6,7,9],
  [1,5,6,8],
  [0,4,5,7],
  [3,4,6,12],
  [2,3,5,11],
  [1,2,4,10]];
const n = linesAtPoint.length;
const vertex = (v) => 1n << BigInt(v);
const pair = (a, b) => vertex(a) | vertex(b);
const allEdges = new Set();
for (const [p, lines] of linesAtPoint.entries()) {
  assert.equal(new Set(lines).size, 4);
  assert(lines.includes((n - p) % n)); // Tretton par med olika punkter och linjer.
  for (const line of lines) allEdges.add(pair(p, n + line));
}
assert.equal(allEdges.size, 52);
for (let a = 0; a < n; a++) {
  for (let b = a + 1; b < n; b++) {
    const common = linesAtPoint[a].filter(l => linesAtPoint[b].includes(l));
    assert.equal(common.length, 1); // En rektangel med två på båda sidor är omöjlig.
  }
}

// Varje tråd lagrar alla minimala uppsättningar av tryckta knappar som tänder den.
// Det beskriver värdet på alla indata: en tråd lyser precis när någon sådan mängd ingår.
const wires = Array.from({length: 2 * n}, (_, i) => [vertex(i)]);
function gate(op, left, right) {
  const a = wires[left], b = wires[right];
  const proposed = op === 'or' ? [...a, ...b] : a.flatMap(x => b.map(y => x | y));
  const distinct = [...new Set(proposed)];
  const minimal = distinct.filter(x => !distinct.some(y => y !== x && (y & x) === y));
  wires.push(minimal);
  return wires.length - 1;
}
function joinByOr(wireNumbers) {
  return wireNumbers.reduce((left, right) => gate('or', left, right));
}
const stars = linesAtPoint.map((lines, point) => {
  const anyLine = joinByOr(lines.map(l => n + l));
  return gate('and', point, anyLine);
});
const output = joinByOr(stars);
assert.equal(wires.length - 2 * n, 64);
assert.deepEqual(new Set(wires[output]), allEdges);

// Fixera vilka punkter som är centra. Alla linjer med en otäckt kant är då tvingade.
let min = 2 * n, count = 0;
for (let mask = 0; mask < 2 ** n; mask++) {
  const forcedLines = new Set();
  let chosen = 0;
  for (const [p, lines] of linesAtPoint.entries()) {
    if ((mask & (1 << p)) !== 0) chosen++;
    else for (const l of lines) forcedLines.add(l);
  }
  const cost = chosen + forcedLines.size;
  if (cost < min) { min = cost; count = 1; }
  else if (cost === min) count++;
}
assert.equal(min, 13);
assert.equal(count, 2);
console.log('52 kanter, 13 disjunkta par, ingen 2 x 2-rektangel.');
console.log('64-grindskretsen har exakt de 52 önskade minimala sätten att tändas.');
console.log('Alla 8192 punktval kontrollerade. Minsta täckning har 13 centra. Exakt två täckningar når dit.');
