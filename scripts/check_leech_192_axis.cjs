// Keep the length-192 replay command used in the published proof notes.
'use strict';

const checkShellAxis = require('./check_leech_shell_axis.cjs');
const record = require('../docs/leech-symmetry-verification-2026-11-21-norm192-dot-layers.json');
if (process.argv.length !== 3) throw new Error('Usage: node scripts/check_leech_192_axis.cjs PATH_TO_PLAYGROUND');
checkShellAxis(process.argv[2], record.playground_norm192_layers);
