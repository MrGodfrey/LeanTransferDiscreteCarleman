#!/usr/bin/env python3
"""Count repository-owned Lean, excluding dependencies, at an exact git revision.

Noncomment lines retain code beside comments; Lean's nested /- -/ comments,
-- line comments, string literals and escaped string characters are handled.
"""
import argparse
import json
import subprocess


def without_comments(source):
    result = []
    offset = depth = 0
    quoted = False
    while offset < len(source):
        pair = source[offset:offset + 2]
        char = source[offset]
        if depth:
            if pair == '/-':
                depth += 1
                offset += 2
            elif pair == '-/':
                depth -= 1
                offset += 2
            else:
                if char == '\n':
                    result.append(char)
                offset += 1
        elif quoted:
            result.append(char)
            if char == '\\' and offset + 1 < len(source):
                result.append(source[offset + 1])
                offset += 2
                continue
            if char == '"':
                quoted = False
            offset += 1
        elif pair == '/-':
            depth = 1
            offset += 2
        elif pair == '--':
            newline = source.find('\n', offset)
            offset = len(source) if newline == -1 else newline
        else:
            result.append(char)
            quoted = char == '"'
            offset += 1
    return ''.join(result)


def count(revision):
    def git(*args):
        return subprocess.check_output(['git', *args], text=True)
    sha = git('rev-parse', revision).strip()
    files = [f for f in git('ls-tree', '-r', '--name-only', sha).splitlines()
             if f.endswith('.lean') and (f == 'Carleman.lean' or f.startswith(('Carleman/', 'tools/')))]
    totals = {key: dict(files=0, physical=0, nonblank_noncomment=0)
              for key in ('all', 'library', 'audit_tools')}
    for path in files:
        source = git('show', f'{sha}:{path}')
        physical = len(source.splitlines())
        code = sum(bool(line.strip()) for line in without_comments(source).splitlines())
        for category in ('all', 'audit_tools' if path.startswith('tools/') else 'library'):
            totals[category]['files'] += 1
            totals[category]['physical'] += physical
            totals[category]['nonblank_noncomment'] += code
    return dict(checked_sha=sha, method='repository-owned Lean; nested comments and strings parsed', **totals)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('revision', nargs='?', default='HEAD')
    args = parser.parse_args()
    print(json.dumps(count(args.revision), indent=2))
