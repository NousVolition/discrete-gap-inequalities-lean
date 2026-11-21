// Recount one shell along (4, -4, 0, ...) with the playground's Golay words.
'use strict';

const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const vm = require('node:vm');

function checkShellAxis(playground, shell) {
  const site = path.resolve(playground);
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
  const rows = countShellLayers(code, weights, shell.vector_squared_length);
  const expected = Object.entries(shell.counts).map(([k, n]) => [Number(k), n]).sort((a, b) => a[0] - b[0]);
  assert.deepEqual(rows, expected);
  assert.equal(shell.default_count, 0);
  const total = rows.reduce((sum, [, n]) => sum + n, 0);
  assert(Number.isSafeInteger(total));
  assert.equal(total, shell.shell_total);
  console.log(rows.map(([k, n]) => k + '\t' + n).join('\n'));
  console.log(rows.length + ' signed layers along (4, -4, 0, ...), total ' + total);
}

module.exports = checkShellAxis;

if (require.main === module) {
  if (process.argv.length !== 4) {
    throw new Error('Usage: node scripts/check_leech_shell_axis.cjs PATH_TO_PLAYGROUND VERIFICATION_RECORD');
  }
  const record = JSON.parse(fs.readFileSync(process.argv[3], 'utf8'));
  const shells = Object.values(record).filter(value =>
    Number.isSafeInteger(value?.vector_squared_length) && record.stage_public_theorems.includes(value.theorem));
  assert.equal(shells.length, 1, 'Expected one shell theorem for this verification record.');
  checkShellAxis(process.argv[2], shells[0]);
}
