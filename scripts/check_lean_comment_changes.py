"""Verify that a wording update changes no Lean code outside comments."""
from pathlib import Path
import hashlib
import json
import subprocess
import sys

root = Path(__file__).resolve().parents[1]
base = sys.argv[1] if len(sys.argv) > 1 else '3407db2750d775fcc351a8a4757c70025f100108'

def git(*args):
    return subprocess.check_output(['git', '-C', str(root), *args]).decode('utf-8').replace('\r\n', '\n')

def without_comments(source):
    out = []
    i = 0
    while i < len(source):
        if source.startswith('/-', i):
            depth = 1
            i += 2
            while depth:
                assert i < len(source), 'Unterminated block comment'
                if source.startswith('/-', i):
                    depth += 1
                    i += 2
                elif source.startswith('-/', i):
                    depth -= 1
                    i += 2
                else:
                    i += 1
        elif source.startswith('--', i):
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        elif source[i] == '"':
            start = i
            i += 1
            while i < len(source):
                if source[i] == '\\':
                    i += 2
                elif source[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
            out.append(source[start:i])
        else:
            out.append(source[i])
            i += 1
    return ''.join(out)

changed = {}
files = git('ls-files', '*.lean').splitlines()
for name in files:
    old = git('show', base + ':' + name)
    new = (root / name).read_text(encoding='utf-8')
    before, after = without_comments(old), without_comments(new)
    assert before == after, f'Lean code changed outside comments: {name}'
    if old != new:
        changed[name] = hashlib.sha256(after.encode('utf-8')).hexdigest()
print(json.dumps({'status': 'PASS', 'base_commit': base, 'lean_files_compared': len(files),
                  'changed_files_code_without_comments_sha256': changed,
                  'scope': 'All tracked Lean files compared with the published base after removing line and nested block comments, preserving strings and all remaining characters. No theorem, definition, proof or compiler option changed. This is a source comparison, not a fresh Lean build.'}, indent=2))
