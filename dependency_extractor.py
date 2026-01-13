#!/usr/bin/env python3
"""
dependency_extractor.py

Extract Rust path dependencies for a given function by analyzing structured VIR files
in `.verus-log` directory. Properly parses S-expressions to extract type mappings,
impl relationships, and cross-module dependencies.

Usage:
    python dependency_extractor.py vostd::ostd::mm::frame::linked_list::LinkedList::push_front

Output: prints dependencies found with accurate type information from VIR parsing
"""
import sys
import os
import re
import json
from collections import defaultdict, deque
from pathlib import Path

ROOT = os.path.abspath(os.path.dirname(__file__))
VERUS_LOG_DIR = os.path.join(ROOT, ".verus-log")

class SExprParser:
    """Simple S-expression parser for VIR files"""
    
    def __init__(self, text):
        self.text = text
        self.pos = 0
        self.length = len(text)
    
    def skip_whitespace(self):
        while self.pos < self.length and self.text[self.pos].isspace():
            self.pos += 1
    
    def parse_string(self):
        """Parse quoted string"""
        if self.pos >= self.length or self.text[self.pos] != '"':
            return None
        self.pos += 1  # skip opening quote
        start = self.pos
        while self.pos < self.length and self.text[self.pos] != '"':
            if self.text[self.pos] == '\\':
                self.pos += 1  # skip escape character
            self.pos += 1
        result = self.text[start:self.pos]
        self.pos += 1  # skip closing quote
        return result
    
    def parse_symbol(self):
        """Parse unquoted symbol"""
        start = self.pos
        while (self.pos < self.length and 
               not self.text[self.pos].isspace() and 
               self.text[self.pos] not in '()'):
            self.pos += 1
        return self.text[start:self.pos]
    
    def parse_list(self):
        """Parse S-expression list"""
        if self.pos >= self.length or self.text[self.pos] != '(':
            return None
        self.pos += 1  # skip opening paren
        result = []
        
        while self.pos < self.length:
            self.skip_whitespace()
            if self.pos >= self.length:
                break
            if self.text[self.pos] == ')':
                self.pos += 1  # skip closing paren
                return result
            elif self.text[self.pos] == '(':
                result.append(self.parse_list())
            elif self.text[self.pos] == '"':
                result.append(self.parse_string())
            else:
                result.append(self.parse_symbol())
        
        return result
    
    def parse(self):
        """Parse the entire expression"""
        self.skip_whitespace()
        if self.pos < self.length and self.text[self.pos] == '(':
            return self.parse_list()
        elif self.pos < self.length and self.text[self.pos] == '"':
            return self.parse_string()
        else:
            return self.parse_symbol()

class SourceCodeAnalyzer:
    """Analyze source code to map impl&%N to actual types"""
    
    def __init__(self):
        self.impl_mappings = {}  # file_path -> {impl_index -> type_info}
    
    def analyze_source_file(self, file_path):
        """Parse source file and extract impl blocks with their types"""
        if file_path in self.impl_mappings:
            return self.impl_mappings[file_path]
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                content = f.read()
            
            mappings = {}
            # Simple pattern - just find lines starting with impl
            impl_pattern = r'^\s*impl\b'
            
            impl_index = 0
            for line in content.split('\n'):
                if re.match(impl_pattern, line):
                    impl_line = line.strip()
                    
                    # 两种impl模式:
                    # 1. impl Trait for Type -> Type是我们要的类型
                    # 2. impl Type -> Type是我们要的类型
                    type_name = "Unknown"
                    
                    if ' for ' in impl_line:
                        # Pattern 1: impl ... for TypeName
                        for_match = re.search(r'\bfor\s+([A-Z][A-Za-z0-9_]*)', impl_line)
                        if for_match:
                            type_name = for_match.group(1)
                    else:
                        # Pattern 2: impl TypeName (没有for的情况)
                        # 移除impl和泛型约束，然后提取类型名
                        impl_part = re.sub(r'^\s*impl\s*', '', impl_line)  # 移除开头的impl
                        
                        # 如果有泛型约束<...>，移除它
                        if impl_part.startswith('<'):
                            # 找到匹配的>，考虑嵌套
                            bracket_count = 0
                            i = 0
                            for i, char in enumerate(impl_part):
                                if char == '<':
                                    bracket_count += 1
                                elif char == '>':
                                    bracket_count -= 1
                                    if bracket_count == 0:
                                        break
                            
                            if bracket_count == 0:
                                impl_part = impl_part[i+1:].strip()
                        
                        # 从剩余部分提取第一个类型名
                        type_match = re.match(r'\s*([A-Z][A-Za-z0-9_]*)', impl_part)
                        if type_match:
                            type_name = type_match.group(1)
                    
                    mappings[impl_index] = type_name
                    impl_index += 1
            
            self.impl_mappings[file_path] = mappings
            return mappings
            
        except Exception:
            return {}
    
    def get_impl_type(self, module_path, impl_num):
        """Get the actual type for impl&%N in a given module"""
        # Convert module path to source file path
        # lib::aster_common::mm::frame::unique -> vostd/src/aster_common/mm/frame/unique.rs
        if not module_path.startswith('lib::'):
            return None
        
        path_parts = module_path[5:].split('::')  # Remove 'lib::'
        source_file = Path('vostd/src') / Path(*path_parts).with_suffix('.rs')
        
        if not source_file.exists():
            # Try other possible locations
            for base_path in ['kernel/src', 'osdk/src']:
                alt_file = Path(base_path) / Path(*path_parts).with_suffix('.rs')
                if alt_file.exists():
                    source_file = alt_file
                    break
        
        if not source_file.exists():
            return None
        
        mappings = self.analyze_source_file(source_file)
        return mappings.get(impl_num)

class VIRAnalyzer:
    """Analyzer for VIR file structure"""
    
    def __init__(self):
        self.function_defs = {}  # function path -> definition
        self.datatype_defs = {}  # type path -> definition
        self.trait_defs = {}     # trait path -> definition
        self.dependencies = defaultdict(set)  # function -> set of dependencies
        self.source_analyzer = SourceCodeAnalyzer()
    
    def clean_path(self, path):
        """Convert VIR path format to Rust format"""
        if not path or not path.startswith('lib!'):
            return None
        clean = path[4:].replace('.', '::').rstrip(':').rstrip('::')
        return f"lib::{clean}" if clean else None
    
    def extract_impl_mappings(self, expr):
        """Extract impl&%N to type mappings from VIR expression"""
        if not isinstance(expr, list):
            return
        
        # Look for function definitions that can help us map impl&%N to types
        if len(expr) >= 3 and expr[0] == 'Function':
            func_path = None
            func_params = []
            
            for i in range(1, len(expr)):
                if expr[i] == ':name' and i + 1 < len(expr):
                    if isinstance(expr[i + 1], list) and expr[i + 1][0] == 'Fun':
                        func_path = self._extract_path_from_expr(expr[i + 1])
                elif expr[i] == ':params' and i + 1 < len(expr):
                    func_params = expr[i + 1]
            
            # If this is an impl&%N function, try to infer the type from context
            if func_path and 'impl&%' in func_path:
                impl_match = re.search(r'impl&%(\d+)', func_path)
                if impl_match:
                    impl_num = impl_match.group(1)
                    # Look for type information in the function path or parameters
                    # No longer store type mappings in VIR analyzer - use source code analysis instead
        
        # Recursively process nested expressions
        if isinstance(expr, list):
            for item in expr:
                self.extract_impl_mappings(item)
    
    def _infer_type_from_context(self, func_path, params):
        """Infer the type that an impl&%N refers to from function context"""
        # This is a fallback method when source code analysis fails
        # Try to extract basic type info from the module path
        parts = func_path.split('.')
        if len(parts) >= 3:
            module_part = parts[-3]  # Get the part before impl&%N
            
            # Generic fallback: convert snake_case to PascalCase
            if '_' in module_part:
                type_name = ''.join(word.capitalize() for word in module_part.split('_'))
                return type_name
            else:
                return module_part.capitalize()
        
        return None
    
    def _extract_type_from_param(self, param):
        """Extract type information from a parameter definition"""
        if isinstance(param, list):
            for item in param:
                if isinstance(item, list) and len(item) >= 3:
                    if item[0] == 'Dt' and item[1] == 'Path':
                        path = item[2]
                        if 'lib!' in path:
                            clean_path = self.clean_path(path)
                            if clean_path:
                                parts = clean_path.split('::')
                                return parts[-1] if parts else None
        return None
    
    def _extract_path_from_expr(self, expr):
        """Extract path string from VIR path expression"""
        if isinstance(expr, list):
            for item in expr:
                if isinstance(item, str) and 'lib!' in item:
                    return item
        return None
    
    def _extract_type_info(self, expr):
        """Extract type information from VIR type expression"""
        if isinstance(expr, list):
            if len(expr) >= 2 and expr[0] == 'Datatype':
                # Look for (Dt Path "lib!...")
                for item in expr:
                    if isinstance(item, list) and len(item) >= 3 and item[0] == 'Dt' and item[1] == 'Path':
                        path = self.clean_path(item[2])
                        if path:
                            # Extract just the type name
                            parts = path.split('::')
                            return parts[-1] if parts else None
        return None
    
    def extract_function_definition(self, expr):
        """Extract function definition from VIR expression"""
        if not isinstance(expr, list) or len(expr) < 2:
            return
        
        if expr[0] == 'Function':
            func_path = None
            func_body = None
            
            for i in range(1, len(expr)):
                if expr[i] == ':name' and i + 1 < len(expr):
                    if isinstance(expr[i + 1], list) and expr[i + 1][0] == 'Fun':
                        func_path = self._extract_path_from_expr(expr[i + 1])
                elif expr[i] == ':body' and i + 1 < len(expr):
                    func_body = expr[i + 1]
            
            if func_path:
                clean_path = self.clean_path(func_path)
                if clean_path:
                    self.function_defs[clean_path] = {
                        'raw_path': func_path,
                        'body': func_body,
                        'definition': expr
                    }
        
        # Recursively process nested expressions
        if isinstance(expr, list):
            for item in expr:
                self.extract_function_definition(item)

    def extract_dependencies_from_body(self, body_expr, base_module=None):
        """Extract dependencies from function body expression"""
        dependencies = set()
        
        if not isinstance(body_expr, list):
            return dependencies
        
        # Look for function calls, type references, etc.
        self._collect_dependencies_recursive(body_expr, dependencies)
        
        return dependencies
    
    def _collect_dependencies_recursive(self, expr, dependencies):
        """Recursively collect dependencies from expression"""
        if not isinstance(expr, list):
            return
        
        # Look for various dependency patterns
        if len(expr) >= 3:
            # Function calls: (Fun :path "lib!...")
            if expr[0] == 'Fun' and expr[1] == ':path':
                path = self.clean_path(expr[2])
                if path:
                    dependencies.add(path)
            
            # Datatype references: (Dt Path "lib!...")
            elif expr[0] == 'Dt' and expr[1] == 'Path':
                path = self.clean_path(expr[2])
                if path:
                    dependencies.add(path)
            
            # Trait references: (TraitId Path "lib!...")
            elif expr[0] == 'TraitId' and expr[1] == 'Path':
                path = self.clean_path(expr[2])
                if path:
                    dependencies.add(path)
        
        # Recursively process all sub-expressions
        for item in expr:
            if isinstance(item, list):
                self._collect_dependencies_recursive(item, dependencies)
    
    def analyze_vir_file(self, file_path):
        """Analyze a complete VIR file"""
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            # Parse the VIR file as S-expressions
            parser = SExprParser(content)
            
            # VIR files can contain multiple top-level expressions
            expressions = []
            while parser.pos < parser.length:
                parser.skip_whitespace()
                if parser.pos >= parser.length:
                    break
                expr = parser.parse()
                if expr:
                    expressions.append(expr)
            
            # Extract information from all expressions
            for expr in expressions:
                self.extract_impl_mappings(expr)
                self.extract_function_definition(expr)
            
            pass  # Analysis complete
            
        except Exception as e:
            print(f"Error analyzing {file_path}: {e}")
    
    def clean_verus_artifacts(self, path):
        """Remove Verus internal artifacts from function/type names"""
        if not path:
            return path
        
        # Remove _VERUS_VERIFIED_ prefix
        path = re.sub(r'_VERUS_VERIFIED_', '', path)
        
        # Replace %default% with :: for trait method calls
        # impl&%20%default%model -> impl&%20::model
        path = re.sub(r'%default%', '::', path)
        
        # Remove other Verus internal artifacts if needed
        # path = re.sub(r'_VERUS_[A-Z_]+_', '', path)
        
        return path
    
    def resolve_impl_path(self, path):
        """Resolve impl&%N paths to actual types using source code analysis"""
        if 'impl&%' not in path:
            return self.clean_verus_artifacts(path)
        
        # Make a copy to work with
        resolved_path = path
        
        # Extract module path for source code analysis
        # Remove function name AND impl&%N part
        path_parts = path.split('::')
        module_parts = []
        for part in path_parts[:-1]:  # Remove function name
            if not part.startswith('impl&%'):
                module_parts.append(part)
        module_str = '::'.join(module_parts)
        
        # Find and replace all impl&%N patterns
        impl_pattern = r'impl&%(\d+)'
        matches = list(re.finditer(impl_pattern, path))
        
        # Process matches in reverse order to avoid position shifting
        for match in reversed(matches):
            impl_key = match.group(0)  # e.g., "impl&%13"
            impl_num = int(match.group(1))  # e.g., 13
            
            # Try source code analysis
            actual_type = self.source_analyzer.get_impl_type(module_str, impl_num)
            
            # Apply the replacement if we found a mapping
            if actual_type and actual_type != impl_key and not actual_type.startswith('impl&%'):
                # Replace the impl&%N with the actual type
                start, end = match.span()
                resolved_path = resolved_path[:start] + actual_type + resolved_path[end:]
                
        return self.clean_verus_artifacts(resolved_path)

class DependencyExtractor:
    """Main dependency extraction orchestrator"""
    
    def __init__(self):
        self.analyzer = VIRAnalyzer()
        self.vir_files_cache = {}
    
    def find_relevant_vir_files(self, target_function):
        """Find all VIR files that might contain relevant dependencies"""
        target_parts = target_function.split('::')
        if len(target_parts) < 4:
            return []
        
        vir_files = []
        vostd_dir = os.path.join(VERUS_LOG_DIR, 'vostd')
        
        if not os.path.exists(vostd_dir):
            print(f"Error: {vostd_dir} does not exist")
            return []
        
        # Primary target file
        module_file = '__'.join(target_parts[1:-2]) + '-poly.vir'
        primary_file = os.path.join(vostd_dir, module_file)
        if os.path.exists(primary_file):
            vir_files.append(primary_file)
        
        # Find related files (same parent modules)
        for file_name in os.listdir(vostd_dir):
            if file_name.endswith('-poly.vir'):
                file_path = os.path.join(vostd_dir, file_name)
                # Include files from related modules
                module_parts = file_name[:-9].split('__')  # remove -poly.vir
                if any(part in target_parts for part in module_parts):
                    if file_path not in vir_files:
                        vir_files.append(file_path)
        
        return vir_files
    
    def check_air_smt_files(self, target_function):
        """Check if AIR/SMT2 files provide additional useful information"""
        air_info = {}
        target_parts = target_function.split('::')
        
        # Look for corresponding AIR/SMT2 files
        vostd_dir = os.path.join(VERUS_LOG_DIR, 'vostd')
        if os.path.exists(vostd_dir):
            module_base = '__'.join(target_parts[1:-2])
            for ext in ['.air', '.smt2']:
                for suffix in ['', '-poly']:
                    air_file = os.path.join(vostd_dir, f"{module_base}{suffix}{ext}")
                    if os.path.exists(air_file):
                        try:
                            with open(air_file, 'r', encoding='utf-8', errors='ignore') as f:
                                content = f.read()
                            # Basic analysis of AIR/SMT content
                            air_info[air_file] = {
                                'functions': len(re.findall(r'declare-fun', content)),
                                'calls': len(re.findall(r'\([a-zA-Z_]', content)),
                                'size': len(content)
                            }
                        except Exception as e:
                            air_info[air_file] = {'error': str(e)}
        
        return air_info

    def extract_dependencies(self, target_function):
        """Extract complete dependency graph for target function"""
        print(f"Analyzing dependencies for: {target_function}")
        
        # 1. Find all relevant VIR files
        vir_files = self.find_relevant_vir_files(target_function)
        
        # 2. Analyze all VIR files to build type mappings and function definitions
        for vir_file in vir_files:
            self.analyzer.analyze_vir_file(vir_file)
        
        # 3. Check AIR/SMT2 files for additional info
        air_info = self.check_air_smt_files(target_function)
        
        # 4. Find the target function and extract its dependencies
        dependencies = set()
        target_clean = self._convert_target_to_vir_format(target_function)
        
        # Look for exact matches and VERUS_VERIFIED versions
        for func_path, func_info in self.analyzer.function_defs.items():
            if self._matches_target(func_path, func_info['raw_path'], target_function):
                
                # Extract dependencies from function body
                body_deps = self.analyzer.extract_dependencies_from_body(func_info['body'])
                dependencies.update(body_deps)
                
                # Also analyze the complete function definition
                def_deps = set()
                self.analyzer._collect_dependencies_recursive(func_info['definition'], def_deps)
                dependencies.update(def_deps)
        
        if not dependencies:
            print(f"Target function {target_function} not found in VIR files")
            return set()
        
        # 5. Resolve impl&%N paths to actual types
        resolved_dependencies = set()
        # Resolve impl&%N mappings
        for dep in dependencies:
            resolved = self.analyzer.resolve_impl_path(dep)
            resolved_dependencies.add(resolved)
        
        # 6. Resolve transitive dependencies
        all_dependencies = self._resolve_transitive_dependencies(resolved_dependencies)
        
        return all_dependencies
    
    def _convert_target_to_vir_format(self, target_function):
        """Convert Rust function path to VIR format"""
        parts = target_function.split('::')
        if len(parts) >= 4:
            # vostd::ostd::mm::frame::LinkedList::push_front
            # -> lib!ostd.mm.frame.impl&%0.push_front.
            func_name = parts[-1]
            module_parts = parts[1:-2]  # skip vostd and function name
            return f"lib!{'.'.join(module_parts)}.impl&%0.{func_name}."
        return target_function
    
    def _matches_target(self, func_path, raw_vir_path, target_function):
        """Check if function path matches target"""
        target_parts = target_function.split('::')
        func_name = target_parts[-1]
        
        # Check if this function matches our target
        if func_name in raw_vir_path:
            # Check for exact match or _VERUS_VERIFIED_ version
            if (f".{func_name}." in raw_vir_path or 
                f"._VERUS_VERIFIED_{func_name}." in raw_vir_path):
                # Also check module path
                module_parts = target_parts[1:-2]
                module_pattern = '.'.join(module_parts)
                if module_pattern in raw_vir_path:
                    return True
        return False
    
    def _resolve_transitive_dependencies(self, direct_deps):
        """Resolve transitive dependencies by following the dependency graph"""
        all_deps = set(direct_deps)
        queue = deque(direct_deps)
        seen = set()
        
        while queue:
            current = queue.popleft()
            if current in seen:
                continue
            seen.add(current)
            
            # Find this dependency in our function definitions
            for func_path, func_info in self.analyzer.function_defs.items():
                if current in func_path:
                    # Extract dependencies from this function
                    new_deps = self.analyzer.extract_dependencies_from_body(func_info['body'])
                    for dep in new_deps:
                        resolved_dep = self.analyzer.resolve_impl_path(dep)
                        if resolved_dep not in all_deps:
                            all_deps.add(resolved_dep)
                            queue.append(resolved_dep)
        
        return sorted(all_deps)

def main():
    if len(sys.argv) < 2:
        print("Usage: python dependency_extractor.py <fully::qualified::path>")
        print("Example: python dependency_extractor.py vostd::ostd::mm::frame::linked_list::LinkedList::push_front")
        sys.exit(2)
    
    target = sys.argv[1]

    if not os.path.isdir(VERUS_LOG_DIR):
        print(f"Error: {VERUS_LOG_DIR} does not exist. Run Verus verification first.")
        sys.exit(1)

    # Create dependency extractor and analyze
    extractor = DependencyExtractor()
    
    print(f"Analyzing dependencies for: {target}")
    print("=" * 60)
    
    dependencies = extractor.extract_dependencies(target)
    
    print(f"\n=== Dependencies for {target} ===")
    for dep in dependencies:
        print(dep)
    
    print(f"\nTotal: {len(dependencies)} dependencies found")

if __name__ == '__main__':
    main()
