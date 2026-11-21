// Recount one axis with the playground's Golay words and shell counter.
'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');

if (process.argv.length !== 3) throw new Error('Usage: node scripts/check_leech_192_axis.cjs PATH_TO_PLAYGROUND');
const site = path.resolve(process.argv[2]);
const html = fs.readFileSync(path.join(site, 'index.html'), 'utf8');
const tab = html.match(/<template id="page-src-leech">([\s\S]*?)<\/template>/)[1];
const start = tab.indexOf('const Q = [];');
const end = tab.indexOf('const N = 1104', start);
assert(start >= 0 && end > start);
const {code, weights} = new vm.Script(tab.slice(start, end) + '\n({code, weights})')
  .runInNewContext({}, {timeout: 15000});
assert.equal(code.length, 4096);
assert.equal(new Set(code).size, 4096);

const countShellLayers = require(path.join(site, 'tests/leech-shell-layers.cjs'));
const rows = countShellLayers(code, weights, 192);
const record = require('../docs/leech-symmetry-verification-2026-11-21-norm192-dot-layers.json');
const shell = record.playground_norm192_layers;
const expected = Object.entries(shell.counts).map(([k, n]) => [Number(k), n]).sort((a, b) => a[0] - b[0]);
assert.deepEqual(rows, expected);
const total = rows.reduce((sum, [, n]) => sum + n, 0);
assert(Number.isSafeInteger(total));
assert.equal(total, shell.shell_total);
console.log(rows.map(([k, n]) => k + '\t' + n).join('\n'));
console.log('19 signed layers along (4, -4, 0, ...), total ' + total);
