#!/usr/bin/env python3
"""
dependency_extractor.py

Extract Rust path dependencies for a given function by analyzing VIR files
in `.verus-log` directory. Looks for call graphs, function dependencies,
and type information from Verus verification intermediate representation.

Usage:
    python dependency_extractor.py vostd::ostd::mm::frame::linked_list::LinkedList::push_front

Output: prints dependencies found in VIR files (functions, types, traits, impls)
"""
import sys
import os
import re
import json
from collections import defaultdict, deque

ROOT = os.path.abspath(os.path.dirname(__file__))
VERUS_LOG_DIR = os.path.join(ROOT, ".verus-log")

def walk_vir_files(root):
    """Walk through all files in .verus-log directory"""
    for dirpath, dirs, files in os.walk(root):
        for f in files:
            path = os.path.join(dirpath, f)
            try:
                with open(path, "r", encoding="utf-8", errors="ignore") as fh:
                    yield path, fh.read()
            except OSError:
                continue

def parse_vir_dependencies(text, target_function):
    """Parse VIR files for type and function dependencies"""
    dependencies = set()
    
    # VIR contains structured info like:
    # :typ (Typ Datatype (Dt Path "lib!aster_common.mm.frame.LinkedList.") 
    dt_paths = re.findall(r'Dt Path "([^"]*)"', text)
    for path in dt_paths:
        # Convert lib!path.to.Type. format to path::to::Type
        clean_path = path.replace('!', '::').replace('.', '').rstrip(':')
        if clean_path and clean_path != "lib":
            dependencies.add(clean_path)
    
    # Look for trait implementations
    impl_paths = re.findall(r'ImplPath.*?"([^"]*)"', text) 
    for path in impl_paths:
        clean_path = path.replace('!', '::').replace('.', '').rstrip(':')
        if clean_path:
            dependencies.add(clean_path)
            
    # Look for function calls in VIR
    fun_paths = re.findall(r'Fun :path "([^"]*)"', text)
    for path in fun_paths:
        clean_path = path.replace('!', '::').replace('.', '').rstrip(':')
        if clean_path:
            dependencies.add(clean_path)
    
    return dependencies

def parse_air_dependencies(text, target_function):
    """Parse AIR/SMT files for function calls and type dependencies"""
    dependencies = set()
    
    # AIR contains function declarations and calls
    # Look for declare-fun and function applications
    declare_funs = re.findall(r'declare-fun\s+[^%]*%([^%\s\)]+)', text)
    for fun in declare_funs:
        clean_path = fun.replace('!', '::').replace('.', '').rstrip(':')
        if clean_path and '::' in clean_path:
            dependencies.add(clean_path)
    
    # Look for function calls/applications
    apply_funs = re.findall(r'%%apply%%.*?([a-zA-Z_][a-zA-Z0-9_]*(?:::[a-zA-Z_][a-zA-Z0-9_]*)+)', text)
    for fun in apply_funs:
        if fun:
            dependencies.add(fun)
            
    return dependencies

def parse_type_definitions(text):
    """Parse VIR text to find type definitions"""
    type_defs = {}
    lines = text.splitlines()
    
    for line in lines:
        # Look for struct definitions
        struct_match = re.search(r'struct\s+([A-Za-z_][A-Za-z0-9_]*)', line)
        if struct_match:
            type_defs[struct_match.group(1)] = 'struct'
            
        # Look for enum definitions  
        enum_match = re.search(r'enum\s+([A-Za-z_][A-Za-z0-9_]*)', line)
        if enum_match:
            type_defs[enum_match.group(1)] = 'enum'
            
        # Look for type aliases
        type_match = re.search(r'type\s+([A-Za-z_][A-Za-z0-9_]*)', line)
        if type_match:
            type_defs[type_match.group(1)] = 'type'
    
    return type_defs

def resolve_dependencies_recursive(target, all_files):
    """Recursively resolve all dependencies from multiple file types"""
    seen = set()
    queue = deque([target])
    all_dependencies = set()
    
    while queue:
        current = queue.popleft()
        if current in seen:
            continue
        seen.add(current)
        
        # Search for this function/type in all files
        for file_path, content in all_files:
            deps = set()
            
            if file_path.endswith('.vir'):
                deps = parse_vir_dependencies(content, current)
            elif file_path.endswith(('.air', '.smt2')):
                deps = parse_air_dependencies(content, current)
            
            for dep in deps:
                if dep not in seen and len(dep) > 3:  # Filter out very short names
                    queue.append(dep)
                    all_dependencies.add(dep)
    
    return sorted(all_dependencies)

def parse_function_definition(content, target_function):
    """Parse specific function definition from VIR content"""
    function_pattern = re.compile(
        r'\(Function\s+:name\s+\(Fun\s+:path\s+"([^"]+)"\)', 
        re.MULTILINE | re.DOTALL
    )
    
    matches = function_pattern.finditer(content)
    
    # Convert target function to match VIR format
    # vostd::ostd::mm::frame::linked_list::LinkedList::push_front
    # becomes lib!ostd.mm.frame.linked_list.impl&%0.push_front.
    target_parts = target_function.split('::')
    if len(target_parts) >= 4:
        # Extract the function name
        func_name = target_parts[-1]  # push_front
        # Build the expected pattern
        expected_patterns = [
            f"lib!{'.'.join(target_parts[1:-2])}.impl&%0.{func_name}.",
            f"lib!{'.'.join(target_parts[1:-2])}.impl&%0._VERUS_VERIFIED_{func_name}.",
            f"lib!{'.'.join(target_parts[1:])}.{func_name}."
        ]
    else:
        return None, None
    
    for match in matches:
        fun_path = match.group(1)
        # Check if this matches any of our expected patterns
        for pattern in expected_patterns:
            if pattern in fun_path:
                # Found our function, now extract its complete definition
                start_pos = match.start()
                
                # Find the complete function definition by counting parentheses
                paren_count = 0
                pos = start_pos
                in_function = False
                
                while pos < len(content):
                    char = content[pos]
                    if char == '(':
                        paren_count += 1
                        in_function = True
                    elif char == ')':
                        paren_count -= 1
                        if in_function and paren_count == 0:
                            # Found the end of function definition
                            return content[start_pos:pos+1], fun_path
                    pos += 1
    
    return None, None

def extract_dependencies_from_function_def(function_def):
    """Extract dependencies from a specific function definition"""
    dependencies = set()
    
    if not function_def:
        return dependencies
    
    # Extract type paths from the function definition
    # Look for (Dt Path "lib!...") patterns
    dt_paths = re.findall(r'Dt\s+Path\s+"([^"]+)"', function_def)
    for path in dt_paths:
        if path.startswith('lib!'):
            clean = path[4:].replace('.', '::').rstrip(':')
            if clean and '::' in clean:
                dependencies.add('lib::' + clean)
    
    # Look for TraitId Path patterns
    trait_paths = re.findall(r'TraitId\s+Path\s+"([^"]+)"', function_def)
    for path in trait_paths:
        if path.startswith('lib!'):
            clean = path[4:].replace('.', '::').rstrip(':')
            if clean and '::' in clean:
                dependencies.add('lib::' + clean)
    
    # Look for ImplPath patterns
    impl_paths = re.findall(r'ImplPath\s+[^"]*"([^"]+)"', function_def)
    for path in impl_paths:
        if path.startswith('lib!'):
            clean = path[4:].replace('.', '::').rstrip(':')
            if clean and '::' in clean:
                dependencies.add('lib::' + clean)
    
    # Look for function calls in :body if present
    fun_calls = re.findall(r'Fun\s+:path\s+"([^"]+)"', function_def)
    for path in fun_calls:
        if path.startswith('lib!'):
            clean = path[4:].replace('.', '::').rstrip(':')
            if clean and '::' in clean:
                dependencies.add('lib::' + clean)
    
    return dependencies

def resolve_transitive_dependencies(dependencies, content):
    """Resolve transitive dependencies by following type and trait definitions"""
    all_deps = set(dependencies)
    queue = deque(dependencies)
    seen = set()
    
    while queue:
        current = queue.popleft()
        if current in seen:
            continue
        seen.add(current)
        
        # Convert back to VIR format for searching
        vir_path = current.replace('lib::', 'lib!').replace('::', '.') + '.'
        
        # Find definitions of this type/trait in the content
        patterns = [
            rf'Datatype\s+:name\s+\(Dt\s+Path\s+"{re.escape(vir_path)}"',
            rf'Trait\s+:name\s+\(TraitPath\s+"{re.escape(vir_path)}"',
            rf'Function\s+:name\s+\(Fun\s+:path\s+"{re.escape(vir_path)}'
        ]
        
        for pattern in patterns:
            matches = re.finditer(pattern, content, re.MULTILINE)
            for match in matches:
                # Extract definition by finding matching parentheses
                start_pos = match.start()
                paren_count = 0
                pos = start_pos
                
                while pos < len(content):
                    char = content[pos]
                    if char == '(':
                        paren_count += 1
                    elif char == ')':
                        paren_count -= 1
                        if paren_count == 0:
                            definition = content[start_pos:pos+1]
                            # Extract dependencies from this definition
                            new_deps = extract_dependencies_from_function_def(definition)
                            for dep in new_deps:
                                if dep not in all_deps:
                                    all_deps.add(dep)
                                    queue.append(dep)
                            break
                    pos += 1
    
    return sorted(all_deps)

def extract_dependencies_precise(target_function):
    """Precise dependency extraction for a specific function"""
    dependencies = set()
    
    # Convert target to find matching VIR file
    target_parts = target_function.split('::')
    if len(target_parts) >= 4:
        module_file = '__'.join(target_parts[1:-2]) + '-poly.vir'
        file_path = os.path.join(VERUS_LOG_DIR, 'vostd', module_file)
        
        if os.path.exists(file_path):
            print(f"Reading {file_path}")
            try:
                with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                    content = f.read()
                
                # Find the specific function definition
                function_def, found_path = parse_function_definition(content, target_function)
                
                if function_def:
                    print(f"Found function definition: {found_path}")
                    # Extract dependencies only from this function
                    dependencies = extract_dependencies_from_function_def(function_def)
                    print(f"Found {len(dependencies)} direct dependencies")
                    
                    # Also check for _VERUS_VERIFIED_ version
                    verified_target = target_function.replace('::', '.') + '.'
                    verified_pattern = verified_target.replace('.', '\\._VERUS_VERIFIED_')
                    verified_matches = re.finditer(
                        rf'Fun\s+:path\s+"[^"]*{re.escape("_VERUS_VERIFIED_")}[^"]*{re.escape(target_parts[-1])}\."',
                        content
                    )
                    
                    for match in verified_matches:
                        verified_def, verified_path = parse_function_definition(
                            content[match.start()-1000:match.end()+5000], 
                            target_function
                        )
                        if verified_def:
                            print(f"Found verified version: {verified_path}")
                            verified_deps = extract_dependencies_from_function_def(verified_def)
                            dependencies.update(verified_deps)
                            
                    # Resolve transitive dependencies
                    print("Resolving transitive dependencies...")
                    all_dependencies = resolve_transitive_dependencies(dependencies, content)
                    return all_dependencies
                else:
                    print(f"Function {target_function} not found in VIR file")
                    
            except Exception as e:
                print(f"Error reading {file_path}: {e}")
        else:
            print(f"VIR file not found: {file_path}")
    
    return dependencies

def main():
    if len(sys.argv) < 2:
        print("Usage: python dependency_extractor.py <fully::qualified::path>")
        sys.exit(2)
    target = sys.argv[1]

    if not os.path.isdir(VERUS_LOG_DIR):
        print(f"Error: {VERUS_LOG_DIR} does not exist. Run Verus verification first.")
        sys.exit(1)

    # Precise extraction from target function's VIR file
    dependencies = extract_dependencies_precise(target)
    
    print(f"\nDependencies for {target}:")
    for dep in sorted(dependencies):
        print(dep)
    
    print(f"\nTotal: {len(dependencies)} dependencies found")

if __name__ == '__main__':
    main()
