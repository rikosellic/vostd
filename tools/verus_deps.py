#!/usr/bin/env python3
"""
verus_deps.py

Heuristically extract Rust path dependencies for a given fully-qualified symbol
by scanning `.verus-log/vostd` verification files and crate source files.

Usage:
    python tools/verus_deps.py vostd::ostd::mm::frame::linked_list::LinkedList::push_front

Output: prints a sorted list of discovered Rust-style paths and a JSON array to
stdout. This is a best-effort script — it uses regex-based token extraction and
simple impl/trait heuristics.
"""
import sys
import os
import re
import json
from collections import defaultdict, deque

ROOT = os.path.abspath(os.path.dirname(__file__) + os.sep + "..")
VERUS_LOG_DIR = os.path.join(ROOT, ".verus-log", "vostd")
SRC_DIRS = [os.path.join(ROOT, "vostd", "src"), os.path.join(ROOT, "src")]

# Regex to extract Rust-like path tokens (e.g. crate::mod::Type::method)
PATH_RE = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:::[A-Za-z_][A-Za-z0-9_]*)+")

# Simple patterns for definitions/impls/traits/types
IMPL_RE = re.compile(r"impl\s+(?P<head>[^\{]*)\{")
TRAIT_RE = re.compile(r"\btrait\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)")
STRUCT_ENUM_RE = re.compile(r"\b(struct|enum)\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)")
TYPE_RE = re.compile(r"\btype\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)")
FN_RE = re.compile(r"\bfn\s+(?P<name>[A-Za-z_][A-Za-z0-9_]*)")


def walk_text_files(root):
    for dirpath, dirs, files in os.walk(root):
        for f in files:
            path = os.path.join(dirpath, f)
            try:
                with open(path, "r", encoding="utf-8", errors="ignore") as fh:
                    yield path, fh.read()
            except OSError:
                continue


def build_index():
    occurrences = defaultdict(set)  # token -> set(files)
    impl_map = defaultdict(lambda: defaultdict(set))  # file -> impl_head -> set(methods)
    trait_defs = defaultdict(set)  # trait -> files
    type_defs = defaultdict(set)  # type/struct/enum -> files

    # Scan verus logs first (if present)
    if os.path.isdir(VERUS_LOG_DIR):
        for path, text in walk_text_files(VERUS_LOG_DIR):
            for m in PATH_RE.finditer(text):
                occurrences[m.group(0)].add(path)

    # Scan source directories for more context
    for src in SRC_DIRS:
        if not os.path.isdir(src):
            continue
        for path, text in walk_text_files(src):
            # record path-like tokens
            for m in PATH_RE.finditer(text):
                occurrences[m.group(0)].add(path)

            # impl block heuristics: capture 'impl ... { ... }' by scanning lines
            lines = text.splitlines()
            i = 0
            n = len(lines)
            while i < n:
                line = lines[i]
                implm = IMPL_RE.search(line)
                if implm:
                    head = implm.group('head').strip()
                    # collect block until matching braces
                    brace_depth = line.count('{') - line.count('}')
                    j = i + 1
                    methods = set()
                    while j < n and brace_depth > 0:
                        ln = lines[j]
                        brace_depth += ln.count('{') - ln.count('}')
                        fnm = FN_RE.search(ln)
                        if fnm:
                            methods.add(fnm.group('name'))
                        j += 1
                    impl_map[path][head].update(methods)
                    i = j
                    continue

                trm = TRAIT_RE.search(line)
                if trm:
                    trait_defs[trm.group('name')].add(path)

                ser = STRUCT_ENUM_RE.search(line)
                if ser:
                    type_defs[ser.group('name')].add(path)

                tr = TYPE_RE.search(line)
                if tr:
                    type_defs[tr.group('name')].add(path)

                i += 1

    return occurrences, impl_map, trait_defs, type_defs


def extract_line_tokens(text, token):
    # find lines containing token and extract other path-like tokens from those lines
    res = set()
    for line in text.splitlines():
        if token in line:
            for m in PATH_RE.finditer(line):
                res.add(m.group(0))
    return res


def resolve_dependencies(target, occurrences, impl_map, trait_defs, type_defs):
    # BFS over tokens; heuristics: when we see 'Type::method', also add 'Type';
    # when a method of type is found, look for impl blocks that define it.
    seen = set()
    queue = deque([target])
    results = set()

    while queue:
        tok = queue.popleft()
        if tok in seen:
            continue
        seen.add(tok)
        results.add(tok)

        # If tok includes '::', and looks like a method (last segment lowercase), add the containing type path
        parts = tok.split('::')
        if len(parts) >= 2:
            # add all prefixes
            for i in range(1, len(parts)):
                prefix = '::'.join(parts[:i])
                if prefix not in seen:
                    queue.append(prefix)

        # Look up files where token occurs
        files = occurrences.get(tok, set())
        # For each file, extract other tokens on same lines
        for f in files:
            try:
                with open(f, 'r', encoding='utf-8', errors='ignore') as fh:
                    text = fh.read()
            except OSError:
                continue
            toks = extract_line_tokens(text, tok)
            for t in toks:
                if t not in seen:
                    queue.append(t)

        # Heuristic: if token looks like a type, search impl_map for methods defined in impls for that type
        # Try to match simple names (last segment)
        simple = parts[-1]
        for f, heads in impl_map.items():
            for head, methods in heads.items():
                # head might be 'Trait for Type' or 'Type' or '<T> for Type'
                if simple in head or head.endswith(simple) or ('for ' + simple) in head:
                    # add methods and the impl head
                    if head not in seen:
                        queue.append(head)
                    for m in methods:
                        candidate = head + '::' + m
                        if candidate not in seen:
                            queue.append(candidate)

        # If token is a trait name, add its defs
        if tok in trait_defs:
            for f in trait_defs[tok]:
                if f not in seen:
                    queue.append(f)

        # If token is a type name, add its defs
        if simple in type_defs:
            for f in type_defs[simple]:
                if f not in seen:
                    queue.append(f)

    return sorted(results)


def main():
    if len(sys.argv) < 2:
        print("Usage: python tools/verus_deps.py <fully::qualified::path>")
        sys.exit(2)
    target = sys.argv[1]

    occurrences, impl_map, trait_defs, type_defs = build_index()

    deps = resolve_dependencies(target, occurrences, impl_map, trait_defs, type_defs)

    # Print text and JSON
    for d in deps:
        print(d)

    print('\nJSON:')
    print(json.dumps(deps, indent=2))


if __name__ == '__main__':
    main()
