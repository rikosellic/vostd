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

class SpecFunctionAnalyzer:
    """Analyzer for when_used_as_spec annotations"""
    
    def __init__(self, source_analyzer):
        self.source_analyzer = source_analyzer
        self.spec_to_exec_mappings = {}  # spec_function_name -> exec_function_name
    
    def find_when_used_as_spec_mappings(self, module_path):
        """Find all when_used_as_spec mappings in a source file"""
        # Convert module path to source file path
        if not module_path.startswith('lib::'):
            return {}
            
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
            return {}
            
        try:
            with open(source_file, 'r', encoding='utf-8') as f:
                content = f.read()
            
            mappings = {}
            lines = content.split('\n')
            
            for i, line in enumerate(lines):
                # Look for #[verifier::when_used_as_spec(...)]
                when_used_match = re.search(r'#\[verifier::when_used_as_spec\(([^)]+)\)\]', line)
                if when_used_match:
                    spec_func_name = when_used_match.group(1)
                    
                    # Look for the next function definition
                    for j in range(i + 1, min(i + 10, len(lines))):  # Look ahead up to 10 lines
                        next_line = lines[j]
                        # Match function definitions: "pub fn function_name(" or "fn function_name("
                        func_match = re.search(r'(?:pub\s+)?fn\s+([a-zA-Z_][a-zA-Z0-9_]*)\s*\(', next_line)
                        if func_match:
                            exec_func_name = func_match.group(1)
                            mappings[spec_func_name] = exec_func_name
                            break
                        # Skip empty lines and lines with only attributes
                        if next_line.strip() and not next_line.strip().startswith('#['):
                            break
            
            return mappings
            
        except Exception:
            return {}
    
    def get_exec_function_for_spec(self, spec_function_path):
        """Get the execution function path for a given spec function path"""
        # Extract function name and module from the path
        path_parts = spec_function_path.split('::')
        if len(path_parts) < 2:
            return None
            
        spec_func_name = path_parts[-1]
        module_path = '::'.join(path_parts[:-1])
        
        # Get mappings for this module
        mappings = self.find_when_used_as_spec_mappings(module_path)
        
        if spec_func_name in mappings:
            exec_func_name = mappings[spec_func_name]
            return f"{module_path}::{exec_func_name}"
        
        return None

class VIRAnalyzer:
    """Analyzer for VIR file structure"""
    
    def __init__(self):
        self.function_defs = {}  # function path -> definition
        self.datatype_defs = {}  # type path -> definition
        self.trait_defs = {}     # trait path -> definition
        self.trait_impls = defaultdict(list)  # type path -> list of trait impls
        self.dependencies = defaultdict(set)  # function -> set of dependencies
        self.source_analyzer = SourceCodeAnalyzer()
        self.vir_impl_mappings = {}  # impl_path -> type_name
        self.spec_analyzer = SpecFunctionAnalyzer(self.source_analyzer)
    
    def clean_path(self, path):
        """Convert VIR path format to Rust format"""
        if not path or not path.startswith('lib!'):
            return None
        clean = path[4:].replace('.', '::').rstrip(':').rstrip('::')
        return f"lib::{clean}" if clean else None
    
    def extract_impl_mappings(self, expr):
        """Extract impl&%N to type mappings from VIR expression"""
        if not isinstance(expr, list) or len(expr) < 2:
            return
            
        # 1. Processing Function definitions to find impl context
        if expr[0] == 'Function':
            func_path = None
            trait_typ_args = None
            first_param_type = None
            
            # Iterate through key-value pairs in the function expression
            for i in range(1, len(expr)):
                key = expr[i]
                if key == ':name' and i + 1 < len(expr):
                    # Extract function path
                    name_expr = expr[i+1]
                    if isinstance(name_expr, list) and len(name_expr) >= 2 and name_expr[0] == 'Fun':
                         # Search for :path key inside Fun
                        for j in range(1, len(name_expr)):
                            if name_expr[j] == ':path' and j+1 < len(name_expr):
                                func_path = name_expr[j+1]
                                break

                elif key == ':trait_typ_args' and i + 1 < len(expr):
                    # Extract trait type arguments (usually [SelfType, ...])
                    type_args = expr[i+1]
                    if isinstance(type_args, list) and len(type_args) > 0:
                        first_arg = type_args[0]
                        # Try to extract type name from (Typ Datatype (Dt Path "lib!..."))
                        trait_typ_args = self._extract_type_name_from_vir_type(first_arg)

                elif key == ':kind' and i + 1 < len(expr):
                    # Look inside :kind for :trait_typ_args
                    kind_expr = expr[i+1]
                    if isinstance(kind_expr, list):
                        for k in range(len(kind_expr)):
                            if kind_expr[k] == ':trait_typ_args' and k+1 < len(kind_expr):
                                type_args = kind_expr[k+1]
                                if isinstance(type_args, list) and len(type_args) > 0:
                                    first_arg = type_args[0]
                                    trait_typ_args = self._extract_type_name_from_vir_type(first_arg)
                                break

                elif key == ':params' and i + 1 < len(expr):
                    # Extract first parameter type (usually 'self')
                    params = expr[i+1]
                    if isinstance(params, list) and len(params) > 0:
                        first_param = params[0]
                        # (Param :name ... :typ (Typ ...) ...)
                        if isinstance(first_param, list):
                            for j in range(len(first_param)):
                                if first_param[j] == ':typ' and j+1 < len(first_param):
                                     first_param_type = self._extract_type_name_from_vir_type(first_param[j+1])
                                     break
            
            # If we found a path containing impl&%, try to map it
            if func_path and 'impl&%' in func_path:
                # Extract the impl prefix: lib!module.impl&%N
                impl_match = re.search(r'(lib!.*\.impl&%\d+)', func_path)
                if impl_match:
                    impl_key = impl_match.group(1)
                    impl_key_clean = self.clean_path(impl_key + '.') # clean_path expects trailing dot or colon usually
                    if impl_key_clean and impl_key_clean.endswith('::'): 
                        impl_key_clean = impl_key_clean[:-2]
                    elif not impl_key_clean:
                         # Manual clean if clean_path fails/is strict
                         impl_key_clean = impl_key.replace('lib!', 'lib::').replace('.', '::')

                    # Priority 1: Trait Type Args (Function implements Trait for Type)
                    if trait_typ_args:
                        # print(f"DEBUG: Found implicit mapping via trait_typ_args: {impl_key_clean} -> {trait_typ_args}")
                        self.vir_impl_mappings[impl_key_clean] = trait_typ_args
                    # Priority 2: First parameter type (Inherent impl or method)
                    elif first_param_type:
                        # print(f"DEBUG: Found implicit mapping via first_param_type: {impl_key_clean} -> {first_param_type}")
                        self.vir_impl_mappings[impl_key_clean] = first_param_type
        
        # Recursively process nested expressions
        for item in expr:
            if isinstance(item, list):
                self.extract_impl_mappings(item)

    def _extract_type_name_from_vir_type(self, type_expr):
        """Helper to extract simple type name from VIR type expression"""
        # Matches (Typ Datatype (Dt Path "lib!path.TypeName.") ...)
        if isinstance(type_expr, list) and len(type_expr) > 1:
            if type_expr[0] == 'Typ' or type_expr[0] == 'Datatype': # Handle unwrapped Datatype too if needed
                 # Search recursively or specifically
                 pass
            
            # Recursive search for (Dt Path "...")
            return self._find_dt_path_recursive(type_expr)
        return None

    def _find_dt_path_recursive(self, expr):
        if not isinstance(expr, list):
            return None
        if len(expr) >= 3 and expr[0] == 'Dt' and expr[1] == 'Path':
            # Found path: "lib!crate.mod.Type."
            raw_path = expr[2]
            clean = self.clean_path(raw_path)
            if clean:
                return clean.split('::')[-1] # Return just TypeName
        
        for item in expr:
            res = self._find_dt_path_recursive(item)
            if res: return res
        return None

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
    
    def extract_datatype_definitions(self, expr):
        """Extract Datatype definitions from VIR expression to get field dependencies.
        Parses: (Datatype :name (Dt Path "lib!...") ... :variants (...))
        """
        if not isinstance(expr, list) or len(expr) < 2:
            return
        
        if expr[0] == 'Datatype':
            datatype_path = None
            variants = None
            
            # Extract the datatype path and variants
            i = 1
            while i < len(expr):
                if expr[i] == ':name' and i + 1 < len(expr):
                    # Extract path from (Dt Path "lib!...")
                    name_expr = expr[i + 1]
                    if isinstance(name_expr, list) and len(name_expr) >= 3:
                        if name_expr[0] == 'Dt' and name_expr[1] == 'Path':
                            raw_path = name_expr[2]
                            datatype_path = self.clean_path(raw_path)
                    i += 2
                elif expr[i] == ':variants' and i + 1 < len(expr):
                    variants = expr[i + 1]
                    i += 2
                else:
                    i += 1
            
            # Store the datatype definition if we found both path and variants
            if datatype_path and variants:
                self.datatype_defs[datatype_path] = {
                    'path': datatype_path,
                    'variants': variants,
                    'definition': expr
                }
        
        # Recursively process nested expressions
        if isinstance(expr, list):
            for item in expr:
                self.extract_datatype_definitions(item)
    
    def extract_field_dependencies_from_vir(self, type_path):
        """Extract field type dependencies from a Datatype definition in VIR.
        For example, from MetaSlotStorage's variants:
        - FrameLink(StoredLink) → StoredLink
        - PTNode(StoredPageTablePageMeta) → StoredPageTablePageMeta
        """
        field_deps = set()
        
        # Find the datatype definition
        if type_path not in self.datatype_defs:
            return field_deps
        
        datatype_def = self.datatype_defs[type_path]
        variants = datatype_def.get('variants')
        
        if not isinstance(variants, list):
            return field_deps
        
        # Parse each variant
        for variant in variants:
            if not isinstance(variant, list) or len(variant) < 2:
                continue
            
            if variant[0] == 'Variant':
                # Look for :fields in the variant
                i = 1
                while i < len(variant):
                    if variant[i] == ':fields' and i + 1 < len(variant):
                        fields = variant[i + 1]
                        # Extract type paths from fields
                        field_types = self._extract_types_from_fields(fields)
                        field_deps.update(field_types)
                        break
                    i += 1
        
        return field_deps
    
    def _extract_types_from_fields(self, fields):
        """Extract type paths from variant fields.
        Fields format: ((-> 0 (tuple (Typ Datatype (Dt Path "lib!...") ...) ...)))
        """
        type_paths = set()
        
        if not isinstance(fields, list):
            return type_paths
        
        # Recursively search for (Dt Path "lib!...") patterns
        self._find_dt_paths_recursive(fields, type_paths)
        
        return type_paths
    
    def _find_dt_paths_recursive(self, expr, type_paths):
        """Recursively find all (Dt Path "lib!...") patterns and extract clean paths."""
        if not isinstance(expr, list):
            return
        
        # Check if this is a Dt Path pattern
        if len(expr) >= 3 and expr[0] == 'Dt' and expr[1] == 'Path':
            raw_path = expr[2]
            clean = self.clean_path(raw_path)
            if clean:
                # Skip stdlib types
                if not any(clean.startswith(prefix) for prefix in ['vstd::', 'core::', 'std::']):
                    type_paths.add(clean)
            return  # Don't recurse into Dt Path children
        
        # Recurse into all sub-expressions
        for item in expr:
            if isinstance(item, list):
                self._find_dt_paths_recursive(item, type_paths)
    
    def extract_trait_definitions(self, expr):
        """Extract Trait definitions from VIR expression to get associated type constraints.
        Parses: (Trait :name "lib!..." :assoc_typs (...) :assoc_typs_bounds (...))
        """
        if not isinstance(expr, list) or len(expr) < 2:
            return
        
        # Look for (trait (@ ... (Trait :name ...)))
        if expr[0] == 'trait' and len(expr) >= 2:
            trait_expr = expr[1]
            if isinstance(trait_expr, list) and len(trait_expr) >= 2:
                # Handle (@ location (Trait ...))
                if trait_expr[0] == '@' and len(trait_expr) >= 3:
                    trait_def = trait_expr[2]
                    self._parse_trait_definition(trait_def)
                elif trait_expr[0] == 'Trait':
                    self._parse_trait_definition(trait_expr)
        
        # Recursively process nested expressions
        if isinstance(expr, list):
            for item in expr:
                self.extract_trait_definitions(item)
    
    def _parse_trait_definition(self, trait_def):
        """Parse a Trait definition and extract associated type constraints."""
        if not isinstance(trait_def, list) or trait_def[0] != 'Trait':
            return
        
        trait_path = None
        assoc_typs = []
        assoc_typs_bounds = []
        
        # Parse the trait definition
        i = 1
        while i < len(trait_def):
            if trait_def[i] == ':name' and i + 1 < len(trait_def):
                raw_path = trait_def[i + 1]
                if isinstance(raw_path, str):
                    trait_path = self.clean_path(raw_path)
                i += 2
            elif trait_def[i] == ':assoc_typs' and i + 1 < len(trait_def):
                assoc_typs_list = trait_def[i + 1]
                if isinstance(assoc_typs_list, list):
                    assoc_typs = [t for t in assoc_typs_list if isinstance(t, str)]
                i += 2
            elif trait_def[i] == ':assoc_typs_bounds' and i + 1 < len(trait_def):
                assoc_typs_bounds = trait_def[i + 1]
                i += 2
            else:
                i += 1
        
        # Store the trait definition
        if trait_path:
            self.trait_defs[trait_path] = {
                'path': trait_path,
                'assoc_typs': assoc_typs,
                'assoc_typs_bounds': assoc_typs_bounds,
                'definition': trait_def
            }
    
    def extract_trait_constraints_from_vir(self, trait_path):
        """Extract trait constraints from a Trait definition in VIR.
        For example, from OwnerOf's :assoc_typs_bounds, extract:
        - InvView (Owner must implement InvView)
        - View (Owner must implement View)
        - Inv (Owner must implement Inv)
        """
        constraints = set()
        
        if trait_path not in self.trait_defs:
            return constraints
        
        trait_def = self.trait_defs[trait_path]
        assoc_typs_bounds = trait_def.get('assoc_typs_bounds')
        
        if not isinstance(assoc_typs_bounds, list):
            return constraints
        
        # Parse each GenericBound to extract trait paths
        for bound in assoc_typs_bounds:
            if not isinstance(bound, list) or len(bound) < 2:
                continue
            
            if bound[0] == 'GenericBound' and bound[1] == 'Trait':
                # Look for (TraitId Path "lib!...")
                trait_id = None
                if len(bound) >= 3 and isinstance(bound[2], list):
                    trait_id = bound[2]
                
                if isinstance(trait_id, list) and len(trait_id) >= 3:
                    if trait_id[0] == 'TraitId' and trait_id[1] == 'Path':
                        raw_trait_path = trait_id[2]
                        if isinstance(raw_trait_path, str):
                            clean_trait = self.clean_path(raw_trait_path)
                            if clean_trait:
                                constraints.add(clean_trait)
        
        return constraints
    
    def extract_trait_impls(self, expr):
        """Extract trait implementations from VIR.
        Parses: (trait_impl (@ ... (TraitImpl :impl_path ... :trait_path ... :trait_typ_args ...)))
        Stores: type_path -> list of (trait_path, impl_path, source_location)
        """
        if not isinstance(expr, list) or len(expr) < 2:
            return
        
        # Look for (trait_impl (@ location (TraitImpl ...)))
        if expr[0] == 'trait_impl' and len(expr) >= 2:
            trait_impl_expr = expr[1]
            if isinstance(trait_impl_expr, list) and len(trait_impl_expr) >= 3:
                # Handle (@ location (TraitImpl ...))
                if trait_impl_expr[0] == '@':
                    source_loc = trait_impl_expr[1] if len(trait_impl_expr) > 1 else None
                    impl_def = trait_impl_expr[2] if len(trait_impl_expr) > 2 else None
                    if impl_def:
                        self._parse_trait_impl(impl_def, source_loc)
        
        # Recursively process nested expressions
        if isinstance(expr, list):
            for item in expr:
                self.extract_trait_impls(item)
    
    def _parse_trait_impl(self, impl_def, source_loc):
        """Parse a TraitImpl definition and store the mapping."""
        if not isinstance(impl_def, list) or impl_def[0] != 'TraitImpl':
            return
        
        impl_path = None
        trait_path = None
        impl_type = None  # The type implementing the trait
        
        # Parse the impl definition
        i = 1
        while i < len(impl_def):
            if impl_def[i] == ':impl_path' and i + 1 < len(impl_def):
                raw_path = impl_def[i + 1]
                if isinstance(raw_path, str):
                    impl_path = self.clean_path(raw_path)
                i += 2
            elif impl_def[i] == ':trait_path' and i + 1 < len(impl_def):
                raw_path = impl_def[i + 1]
                if isinstance(raw_path, str):
                    trait_path = self.clean_path(raw_path)
                i += 2
            elif impl_def[i] == ':trait_typ_args' and i + 1 < len(impl_def):
                # Extract the type from trait_typ_args
                # Format: ((Typ Datatype (Dt Path "lib!...") ...))
                typ_args = impl_def[i + 1]
                if isinstance(typ_args, list) and len(typ_args) > 0:
                    # Get first type argument (the implementing type)
                    first_arg = typ_args[0]
                    impl_type = self._extract_type_path_from_typ(first_arg)
                i += 2
            else:
                i += 1
        
        # Store if we have all required info
        if impl_type and trait_path:
            if not hasattr(self, 'trait_impls'):
                self.trait_impls = defaultdict(list)
            self.trait_impls[impl_type].append({
                'trait': trait_path,
                'impl_path': impl_path,
                'source_loc': source_loc
            })
    
    def _extract_type_path_from_typ(self, typ_expr):
        """Extract type path from a Typ expression.
        Handles: (Typ Datatype (Dt Path "lib!...") ...)
        """
        if not isinstance(typ_expr, list):
            return None
        
        # Recursively search for (Dt Path "...")
        for item in typ_expr:
            if isinstance(item, list) and len(item) >= 3:
                if item[0] == 'Dt' and item[1] == 'Path':
                    raw_path = item[2]
                    if isinstance(raw_path, str):
                        return self.clean_path(raw_path)
            # Recurse
            if isinstance(item, list):
                result = self._extract_type_path_from_typ(item)
                if result:
                    return result
        return None
    
    def get_trait_impls_for_type(self, type_path):
        """Get all trait implementations for a given type from VIR.
        Returns: list of (trait_path, source_location)
        """
        if not hasattr(self, 'trait_impls'):
            return []
        
        impls = self.trait_impls.get(type_path, [])
        return [(impl['trait'], impl['source_loc']) for impl in impls]

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
                self.extract_datatype_definitions(expr)
                self.extract_trait_definitions(expr)
                self.extract_trait_impls(expr)
            
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

        # Find and replace all impl&%N patterns
        impl_pattern = r'impl&%(\d+)'
        matches = list(re.finditer(impl_pattern, path))
        
        # Process matches in reverse order to avoid position shifting
        for match in reversed(matches):
            impl_key = match.group(0)  # e.g., "impl&%13"
            impl_num = int(match.group(1))  # e.g., 13
            
            # Construct the full impl path key (e.g., lib::aster_common::...::impl&%13)
            # We need to extract the prefix before "impl&%13"
            prefix_end = match.start()
            # Extract everything before the match, assuming it ends with ::
            prefix = path[:prefix_end]
            if prefix.endswith('::'):
                prefix = prefix[:-2] # remove trailing ::
            
            # Try 1: Check VIR mappings first (Robust)
            path_key = f"{prefix}::{impl_key}"
            actual_type = self.vir_impl_mappings.get(path_key)

            if not actual_type:
                # Try 2: Source code analysis (Fallback)
                # Extract module path for source code analysis
                # Remove function name AND impl&%N part
                # Reconstruct module path from prefix
                module_str = prefix
                
                # If prefix contains other impl&%, this might fail, so we rely on VIR mappings primarily
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
        self.source_locations_cache = {}  # Cache for source file locations
    
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
        all_dependencies_list = self._resolve_transitive_dependencies(resolved_dependencies)
        all_dependencies = set(all_dependencies_list)
        
        # 7. Extract trait constraints from trait implementations
        trait_constraint_deps = self.extract_trait_constraints(all_dependencies)
        all_dependencies.update(trait_constraint_deps)
        
        # 8. For each type, find its trait implementations and extract associated types
        type_impl_deps = self.extract_type_implementations(all_dependencies)
        all_dependencies.update(type_impl_deps)
        
        return sorted(all_dependencies)
    
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
        
        # Build a lookup map of resolved path -> function info
        # This allows us to find the function definition for a resolved dependency
        resolved_func_defs = {}
        for func_path, func_info in self.analyzer.function_defs.items():
            resolved_path = self.analyzer.resolve_impl_path(func_path)
            if resolved_path:
                resolved_func_defs[resolved_path] = func_info
        
        while queue:
            current = queue.popleft()
            if current in seen:
                continue
            seen.add(current)
            
            # Check if this is a spec function and find its exec counterpart
            if current.endswith('_spec'):
                exec_func_path = self.analyzer.spec_analyzer.get_exec_function_for_spec(current)
                if exec_func_path and exec_func_path not in all_deps:
                    all_deps.add(exec_func_path)
                    queue.append(exec_func_path)
            
            # Find this dependency in our resolved function definitions
            if current in resolved_func_defs:
                func_info = resolved_func_defs[current]
                
                # Extract dependencies from this function
                new_deps = self.analyzer.extract_dependencies_from_body(func_info['body'])
                for dep in new_deps:
                    resolved_dep = self.analyzer.resolve_impl_path(dep)
                    if resolved_dep not in all_deps:
                        all_deps.add(resolved_dep)
                        queue.append(resolved_dep)
            
            # Fallback: Try to match by substring if exact match failed
            # This helps with some partial path matches if resolution wasn't perfect
            else:
                for func_path, func_info in self.analyzer.function_defs.items():
                    if current in func_path:
                        new_deps = self.analyzer.extract_dependencies_from_body(func_info['body'])
                        for dep in new_deps:
                            resolved_dep = self.analyzer.resolve_impl_path(dep)
                            if resolved_dep not in all_deps:
                                all_deps.add(resolved_dep)
                                queue.append(resolved_dep)
        
        return sorted(all_deps)
    
    def extract_trait_constraints(self, dependencies):
        """Extract additional dependencies from trait constraints.
        For example, if we have 'impl OwnerOf for Type', we need to find:
        1. The OwnerOf trait definition
        2. Its associated type constraints (e.g., type Owner: InvView)
        3. Add those constrained traits to dependencies
        4. For types implementing InvView/View, extract their associated types
        """
        additional_deps = set()
        
        for dep in dependencies:
            # Check if this is a trait implementation
            location = self.find_source_location(dep)
            if location and location.get('in_impl') and location.get('impl_signature'):
                sig = location['impl_signature']
                # Extract trait name from "impl Trait for Type" or "impl<...> Trait for Type"
                if ' for ' in sig:
                    # Parse the trait name and type name
                    parts = sig.split(' for ')
                    trait_part = parts[0].strip()
                    type_part = parts[1].strip() if len(parts) > 1 else ''
                    
                    # Remove 'impl' and generics from trait part
                    trait_part = re.sub(r'^impl\s*(<[^>]+>)?\s*', '', trait_part)
                    trait_name = trait_part.split('<')[0].strip()
                    
                    # Extract the implementing type name (without generics)
                    type_name = type_part.split('<')[0].strip()
                    
                    # Try to find the trait definition and extract its constraints
                    trait_constraints = self._find_trait_constraints(dep, trait_name)
                    additional_deps.update(trait_constraints)
                    
                    # For any trait implementation, extract associated types
                    assoc_types = self._extract_associated_types_from_impl(location['file'], location['line'], type_name)
                    
                    # Add the associated types themselves
                    additional_deps.update(assoc_types)
                    
                    # For each associated type, find its trait implementations
                    for assoc_type_path in assoc_types:
                        assoc_parts = assoc_type_path.split('::')
                        if len(assoc_parts) >= 2:
                            assoc_type_name = assoc_parts[-1]
                            # Find the file where this type is defined
                            module_parts = assoc_parts[1:-1]
                            for base_path in [Path('vostd') / 'src']:
                                file_path = base_path / Path(*module_parts).with_suffix('.rs')
                                if file_path.exists():
                                    # Find all trait implementations for this associated type
                                    type_impls = self._find_type_trait_impls(
                                        file_path, assoc_type_name, '::'.join(assoc_parts[:-1])
                                    )
                                    additional_deps.update(type_impls)
                                    break
        
        return additional_deps
    
    def _find_trait_constraints(self, impl_path, trait_name):
        """Find trait definition and extract associated type constraints using VIR."""
        constraints = set()
        
        # First, try to construct possible trait paths and check VIR
        # Extract module path from impl_path
        parts = impl_path.split('::')
        if len(parts) < 3:
            return constraints
        
        # Try common locations for traits
        module_parts_candidates = []
        for i in range(len(parts) - 1, 1, -1):
            module_parts_candidates.append(parts[1:i])
        
        # Also check common trait locations
        module_parts_candidates.append(['vstd_extra', 'ownership'])
        module_parts_candidates.append(['aster_common', 'mm', 'frame'])
        
        # Try each candidate module path
        for module_parts in module_parts_candidates:
            trait_path = f"lib::{'::'.join(module_parts)}::{trait_name}"
            
            # Try VIR extraction first (more reliable)
            vir_constraints = self.analyzer.extract_trait_constraints_from_vir(trait_path)
            if vir_constraints:
                return vir_constraints
        
        # Fallback to source code parsing if VIR data not available
        for module_parts in module_parts_candidates:
            base_paths = [Path('vostd') / 'src']
            for base_path in base_paths:
                file_path = base_path / Path(*module_parts).with_suffix('.rs')
                if file_path.exists():
                    try:
                        with open(file_path, 'r', encoding='utf-8') as f:
                            content = f.read()
                        
                        # Find the trait definition
                        # Pattern: pub trait TraitName ... { ... }
                        trait_pattern = rf'\bpub\s+trait\s+{re.escape(trait_name)}\b'
                        match = re.search(trait_pattern, content)
                        if match:
                            # Found the trait, now extract associated type constraints
                            # Find the trait block
                            start_pos = match.start()
                            brace_count = 0
                            in_trait = False
                            trait_content = []
                            
                            for i in range(start_pos, len(content)):
                                char = content[i]
                                if char == '{':
                                    brace_count += 1
                                    in_trait = True
                                elif char == '}':
                                    brace_count -= 1
                                    if brace_count == 0 and in_trait:
                                        break
                                if in_trait:
                                    trait_content.append(char)
                            
                            trait_block = ''.join(trait_content)
                            
                            # Extract associated types with constraints
                            # Pattern: type TypeName: Constraint1 + Constraint2;
                            assoc_type_pattern = r'type\s+\w+\s*:\s*([^;]+);'
                            for assoc_match in re.finditer(assoc_type_pattern, trait_block):
                                constraint_str = assoc_match.group(1)
                                # Parse traits from constraint (e.g., "InvView + Sized")
                                trait_constraints = re.findall(r'\b([A-Z][A-Za-z0-9_]*)\b', constraint_str)
                                for constraint_trait in trait_constraints:
                                    if constraint_trait not in ['Self', 'Sized']:  # Skip special types
                                        # Try to construct full path
                                        # First try same module
                                        constraint_path = f"lib::{'::'.join(module_parts)}::{constraint_trait}"
                                        constraints.add(constraint_path)
                            
                            return constraints  # Found the trait, stop searching
                    except Exception:
                        continue
        
        return constraints
    
    def _extract_associated_types_from_impl(self, file_path, line_num, type_name):
        """Extract associated types defined in an impl block.
        For example, from 'impl View for CursorOwner', extract 'type V = CursorModel'.
        """
        assoc_types = set()
        
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            
            # Find the impl block starting at line_num (1-based)
            if line_num < 1 or line_num > len(lines):
                return assoc_types
            
            # Read the impl block
            start_idx = line_num - 1  # Convert to 0-based
            brace_count = 0
            impl_lines = []
            
            for i in range(start_idx, len(lines)):
                line = lines[i]
                impl_lines.append(line)
                
                for char in line:
                    if char == '{':
                        brace_count += 1
                    elif char == '}':
                        brace_count -= 1
                        if brace_count == 0:
                            # End of impl block
                            break
                
                if brace_count == 0 and '{' in ''.join(impl_lines):
                    break
            
            impl_content = ''.join(impl_lines)
            
            # Extract associated type definitions
            # Pattern: type TypeName = SomeType;
            assoc_type_pattern = r'type\s+\w+\s*=\s*([A-Z][A-Za-z0-9_<>]*)'
            for match in re.finditer(assoc_type_pattern, impl_content):
                assoc_type_name = match.group(1)
                # Remove generics for simple matching
                base_type = assoc_type_name.split('<')[0]
                
                # Try to construct full path
                # First, extract the module path from the file path
                file_path_obj = Path(file_path)
                # Get the relative path from vostd/src
                try:
                    vostd_src = Path('vostd') / 'src'
                    if file_path_obj.is_absolute():
                        # Try to make it relative to current working directory
                        rel_to_cwd = file_path_obj.relative_to(Path.cwd())
                        rel_path = str(rel_to_cwd.relative_to(vostd_src)).replace('.rs', '')
                    else:
                        rel_path = str(file_path_obj.relative_to(vostd_src)).replace('.rs', '')
                    
                    # Convert path separators to ::
                    module_parts = rel_path.replace(os.sep, '::')
                    full_path = f"lib::{module_parts}::{base_type}"
                    assoc_types.add(full_path)
                except ValueError:
                    # If can't make relative, skip
                    pass
        
        except Exception:
            pass
        
        return assoc_types
    
    def extract_type_implementations(self, dependencies):
        """For each type in dependencies, find all its trait implementations.
        This helps discover impl View, impl InvView, etc., and their associated types.
        """
        additional_deps = set()
        
        for dep in dependencies:
            # Extract type names from the dependency
            # Skip if it's already an impl
            location = self.find_source_location(dep)
            if location and location.get('in_impl'):
                continue
            
            # Extract potential type names
            parts = dep.split('::')
            if len(parts) < 2:
                continue
            
            # Check if this looks like a type (PascalCase)
            last_part = parts[-1]
            # Type names start with uppercase and typically don't contain all uppercase (constants)
            # Also skip if it looks like a function (lowercase or mixed case with method calls)
            if last_part and last_part[0].isupper() and last_part != last_part.upper():
                # This might be a type, find its implementations
                module_path = '::'.join(parts[:-1])
                type_name = last_part
                
                # Find the file
                if not dep.startswith('lib::'):
                    continue
                
                module_parts = parts[1:-1]
                base_paths = [Path('vostd') / 'src']
                
                for base_path in base_paths:
                    file_path = base_path / Path(*module_parts).with_suffix('.rs')
                    if file_path.exists():
                        # Find trait implementations
                        impl_deps = self._find_type_trait_impls(file_path, type_name, module_path)
                        additional_deps.update(impl_deps)
                        
                        # Find field type dependencies for structs/enums
                        field_deps = self._find_field_type_dependencies(file_path, type_name, module_path)
                        additional_deps.update(field_deps)
                        break
        
        return additional_deps
    
    def _find_field_type_dependencies(self, file_path, type_name, module_path):
        """Find field type dependencies for a struct or enum using VIR file analysis.
        This is more reliable than regex parsing as it uses Verus compiler output.
        For example, from MetaSlotStorage's variants in VIR:
        - FrameLink(StoredLink) → lib::aster_common::mm::frame::linked_list::StoredLink
        - PTNode(StoredPageTablePageMeta) → lib::aster_common::mm::frame::meta::StoredPageTablePageMeta
        """
        field_deps = set()
        
        # Construct the full type path
        type_path = f"{module_path}::{type_name}"
        
        # Try to extract field dependencies from VIR
        vir_field_deps = self.analyzer.extract_field_dependencies_from_vir(type_path)
        if vir_field_deps:
            # VIR extraction succeeded, use it
            return vir_field_deps
        
        # Fallback to regex-based extraction if VIR data not available
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            
            # Find the type definition
            in_type_def = False
            brace_count = 0
            type_lines = []
            
            for line_num, line in enumerate(lines, 1):
                stripped = line.strip()
                
                # Find struct or enum definition
                if not in_type_def:
                    # Match: pub struct TypeName, pub enum TypeName
                    if re.match(rf'\b(?:pub\s+)?(?:struct|enum)\s+{re.escape(type_name)}\s*[<{{]', stripped):
                        in_type_def = True
                        type_lines.append(line)
                        for char in line:
                            if char == '{':
                                brace_count += 1
                            elif char == '}':
                                brace_count -= 1
                        if brace_count == 0:
                            break
                else:
                    type_lines.append(line)
                    for char in line:
                        if char == '{':
                            brace_count += 1
                        elif char == '}':
                            brace_count -= 1
                    if brace_count == 0:
                        break
            
            if not type_lines:
                return field_deps
            
            type_content = ''.join(type_lines)
            
            # Extract type names from fields
            # Pattern 1: field_name: Type or field_name: Generic<Type>
            # Match field declarations: pub field: Type, or just field: Type
            field_pattern = r'\w+\s*:\s*([A-Z][A-Za-z0-9_]*)'
            for match in re.finditer(field_pattern, type_content):
                field_type = match.group(1)
                
                # Skip generic parameters and common stdlib types
                if field_type in ['PPtr', 'PCell', 'PAtomicU64', 'PAtomicU8', 'PhantomData', 'Option', 'Vec', 'Some', 'None']:
                    continue
                
                # Build full path for the field type
                # Assume it's in the same module
                field_path = f"{module_path}::{field_type}"
                field_deps.add(field_path)
            
            # Pattern 2: Enum variant with tuple type: VariantName(Type)
            # Match: VariantName(Type) or VariantName(Type1, Type2)
            variant_pattern = r'\w+\s*\(\s*([A-Z][A-Za-z0-9_]*)'
            for match in re.finditer(variant_pattern, type_content):
                variant_type = match.group(1)
                
                # Skip generic parameters and common stdlib types
                if variant_type in ['PPtr', 'PCell', 'PAtomicU64', 'PAtomicU8', 'PhantomData', 'Option', 'Vec', 'Some', 'None']:
                    continue
                
                # Build full path
                variant_path = f"{module_path}::{variant_type}"
                field_deps.add(variant_path)
            
            # Also extract types from generic parameters
            # Pattern: Generic<Type> or Generic<Type1, Type2>
            generic_pattern = r'<\s*([A-Z][A-Za-z0-9_]*)\s*[,>]'
            for match in re.finditer(generic_pattern, type_content):
                inner_type = match.group(1)
                
                # Skip common stdlib types
                if inner_type in ['PPtr', 'PCell', 'PAtomicU64', 'PAtomicU8', 'PhantomData', 'Option', 'Vec']:
                    continue
                
                # Build full path
                inner_path = f"{module_path}::{inner_type}"
                field_deps.add(inner_path)
        
        except Exception:
            pass
        
        return field_deps
    
    def _find_type_trait_impls(self, file_path, type_name, module_path):
        """Find all trait implementations for a given type.
        Uses VIR first (more reliable, excludes comments), falls back to source code parsing.
        """
        impl_deps = set()
        
        # Construct the full type path
        type_path = f"{module_path}::{type_name}"
        
        # Try VIR first (more reliable)
        vir_impls = self.analyzer.get_trait_impls_for_type(type_path)
        
        if vir_impls:
            # VIR extraction succeeded
            for trait_path, source_loc in vir_impls:
                # Parse source location to get file and line
                # Format: "D:\path\to\file.rs:line:col: line:col (#num)"
                if isinstance(source_loc, str):
                    match = re.match(r'^([^:]+):(\d+):', source_loc)
                    if match:
                        impl_file = match.group(1)
                        line_num = int(match.group(2))
                        
                        # Extract trait name from path
                        trait_parts = trait_path.split('::')
                        if len(trait_parts) >= 2:
                            trait_name = trait_parts[-1]
                            
                            # Build impl signature
                            impl_sig = f"impl {trait_name} for {type_name}"
                            
                            # Add using @ separator format
                            impl_path = f"{module_path}@{impl_sig}"
                            impl_deps.add(impl_path)
                            
                            # Extract associated types from the impl block (still needs source code)
                            try:
                                assoc_types = self._extract_associated_types_from_impl(
                                    impl_file, line_num, type_name
                                )
                                impl_deps.update(assoc_types)
                            except Exception:
                                pass
            return impl_deps
        
        # Fallback to source code parsing if VIR data not available
        try:
            with open(file_path, 'r', encoding='utf-8') as f:
                lines = f.readlines()
            
            # Pre-process to identify comment blocks
            in_block_comment = False
            line_is_comment = []
            
            for line in lines:
                stripped = line.strip()
                
                # Check for block comment start/end
                if '/*' in line:
                    in_block_comment = True
                if '*/' in line:
                    in_block_comment = False
                    line_is_comment.append(True)  # This line is still in comment
                    continue
                
                # Mark if line is in comment
                is_comment = in_block_comment or stripped.startswith('//') or stripped.startswith('*')
                line_is_comment.append(is_comment)
            
            # Find impl blocks for this type
            for line_num, line in enumerate(lines, 1):
                # Skip commented lines
                if line_num - 1 < len(line_is_comment) and line_is_comment[line_num - 1]:
                    continue
                
                stripped = line.strip()
                
                # Match impl Trait for TypeName
                impl_trait_pattern = rf'impl.*\s+for\s+{re.escape(type_name)}\s*[<{{]'
                if re.search(impl_trait_pattern, stripped):
                    # Extract impl signature directly (handles generics correctly)
                    impl_sig = self._extract_impl_signature(stripped)
                    if impl_sig:
                        impl_path = f"{module_path}@{impl_sig}"
                        impl_deps.add(impl_path)
                    
                    # Extract associated types
                    assoc_types = self._extract_associated_types_from_impl(
                        str(file_path), line_num, type_name
                    )
                    impl_deps.update(assoc_types)
        
        except Exception:
            pass
        
        return impl_deps
    
    def find_source_location(self, module_path):
        """Find the source file and line number for a given module path"""
        if module_path in self.source_locations_cache:
            return self.source_locations_cache[module_path]
        
        # Check if this is an impl block path with @ separator
        if '@' in module_path:
            return self._find_impl_block_location_with_separator(module_path)
        
        # Extract parts from module path
        # Format: lib::module::path::Type::function or lib::module::path::function
        # Or: lib::module::path::impl Trait for Type (old format, kept for compatibility)
        if not module_path.startswith('lib::'):
            return None
        
        parts = module_path[5:].split('::')
        if len(parts) < 2:
            return None
        
        # Determine function/item name (last part) and potential type name
        item_name = parts[-1]
        
        # Check if this is an impl block path (old format)
        if item_name.startswith('impl '):
            return self._find_impl_block_location(module_path, parts)
        
        # Try to determine the file path
        # Heuristic: find the module path before the Type/function
        possible_module_paths = []
        
        # Strategy 1: Check if second-to-last part is a type (PascalCase)
        if len(parts) >= 2 and parts[-2][0].isupper():
            # Has a type: lib::module::Type::function
            module_parts = parts[:-2]
            type_name = parts[-2]
        else:
            # No type: lib::module::function or lib::module::CONST
            module_parts = parts[:-1]
            type_name = None
        
        # Build file paths to search
        base_paths = [Path('vostd') / 'src']
        for base_path in base_paths:
            file_path = base_path / Path(*module_parts).with_suffix('.rs')
            if file_path.exists():
                possible_module_paths.append(file_path)
        
        # Search in each possible file for the item definition
        for file_path in possible_module_paths:
            try:
                with open(file_path, 'r', encoding='utf-8') as f:
                    lines = f.readlines()
                
                for line_num, line in enumerate(lines, 1):
                    # Look for various definition patterns
                    
                    # 1. Function definitions: "fn function_name", "pub fn function_name"
                    # Also match Verus-specific modifiers: open spec, closed spec, tracked, etc.
                    func_pattern = rf'\b(?:pub\s+)?(?:const\s+)?(?:open\s+)?(?:closed\s+)?(?:spec\s+)?(?:tracked\s+)?(?:exec\s+)?fn\s+{re.escape(item_name)}\s*[<(]'
                    if re.search(func_pattern, line):
                        # Check if this function is inside an impl block
                        impl_info = self._find_impl_block_start(lines, line_num - 1)
                        if impl_info is not None:
                            # Check if it's a trait impl or inherent impl
                            if impl_info['is_trait_impl']:
                                # Trait impl: show impl block location and signature
                                relative_path = str(file_path).replace('\\', '/')
                                location_info = {
                                    'file': relative_path,
                                    'line': impl_info['line'] + 1,  # Convert to 1-based
                                    'in_impl': True,
                                    'impl_signature': impl_info['signature']
                                }
                            else:
                                # Inherent impl: show function's actual location
                                relative_path = str(file_path).replace('\\', '/')
                                location_info = {
                                    'file': relative_path,
                                    'line': line_num,
                                    'in_impl': False
                                }
                        else:
                            # Standalone function
                            relative_path = str(file_path).replace('\\', '/')
                            location_info = {
                                'file': relative_path,
                                'line': line_num,
                                'in_impl': False
                            }
                        self.source_locations_cache[module_path] = location_info
                        return location_info
                    
                    # 2. Constant definitions: "pub const CONST_NAME", "const CONST_NAME"
                    const_pattern = rf'\b(?:pub\s+)?const\s+{re.escape(item_name)}\s*:'
                    if re.search(const_pattern, line):
                        relative_path = str(file_path).replace('\\', '/')
                        location_info = {
                            'file': relative_path,
                            'line': line_num
                        }
                        self.source_locations_cache[module_path] = location_info
                        return location_info
                    
                    # 2b. extern_const! macro - matches constants within brackets
                    # Matches: pub PAGE_SIZE [PAGE_SIZE_SPEC, CONST_PAGE_SIZE]: usize
                    # Can match either the first name, or names in brackets
                    extern_const_pattern = rf'\b(?:pub\s+)?{re.escape(item_name)}\s*\[[^]]*\]\s*:'
                    if re.search(extern_const_pattern, line):
                        relative_path = str(file_path).replace('\\', '/')
                        location_info = {
                            'file': relative_path,
                            'line': line_num
                        }
                        self.source_locations_cache[module_path] = location_info
                        return location_info
                    
                    # 2c. extern_const! macro - match items inside brackets
                    # Matches: pub NAME [SPEC, CONST_NAME]: where CONST_NAME or SPEC is what we're looking for
                    extern_const_bracket_pattern = rf'\b(?:pub\s+)?[A-Z_]+\s*\[[^]]*{re.escape(item_name)}[^]]*\]\s*:'
                    if re.search(extern_const_bracket_pattern, line):
                        relative_path = str(file_path).replace('\\', '/')
                        location_info = {
                            'file': relative_path,
                            'line': line_num
                        }
                        self.source_locations_cache[module_path] = location_info
                        return location_info
                    
                    # 3. Type definitions: "pub struct TypeName", "pub enum TypeName", "pub trait TypeName"
                    # For traits, allow : for trait bounds
                    type_pattern = rf'\b(?:pub\s+)?(?:struct|enum|union|trait)\s+{re.escape(item_name)}\s*[<{{(:]'
                    if re.search(type_pattern, line):
                        relative_path = str(file_path).replace('\\', '/')
                        location_info = {
                            'file': relative_path,
                            'line': line_num
                        }
                        self.source_locations_cache[module_path] = location_info
                        return location_info
                    
                    # 4. Type alias: "pub type TypeName"
                    alias_pattern = rf'\b(?:pub\s+)?type\s+{re.escape(item_name)}\s*[=<]'
                    if re.search(alias_pattern, line):
                        relative_path = str(file_path).replace('\\', '/')
                        location_info = {
                            'file': relative_path,
                            'line': line_num
                        }
                        self.source_locations_cache[module_path] = location_info
                        return location_info
                
            except Exception:
                continue
        
        # If not found, return None
        self.source_locations_cache[module_path] = None
        return None
    
    def _find_impl_block_location_with_separator(self, module_path):
        """Find the source location of an impl block using @ separator.
        Format: lib::module::path@impl Trait for Type
        """
        if '@' not in module_path:
            return None
        
        # Split by @ to separate module path from impl signature
        parts = module_path.split('@')
        if len(parts) != 2:
            return None
        
        module_part = parts[0]  # e.g., "lib::aster_common::mm::frame::unique"
        impl_signature = parts[1]  # e.g., "impl<M: ...> View for UniqueFrameOwner<M>"
        
        # Extract module parts
        if not module_part.startswith('lib::'):
            return None
        
        module_parts = module_part[5:].split('::')  # Remove 'lib::' and split
        
        # Build file path
        base_paths = [Path('vostd') / 'src']
        for base_path in base_paths:
            file_path = base_path / Path(*module_parts).with_suffix('.rs')
            if file_path.exists():
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        lines = f.readlines()
                    
                    # Search for the impl block
                    for line_num, line in enumerate(lines, 1):
                        stripped = line.strip()
                        
                        # Match impl blocks
                        if stripped.startswith('impl'):
                            # Extract the impl signature from this line
                            current_sig = self._extract_impl_signature(stripped)
                            if current_sig:
                                # Normalize both signatures for comparison (remove extra spaces)
                                normalized_current = ' '.join(current_sig.split())
                                normalized_target = ' '.join(impl_signature.split())
                                
                                if normalized_current == normalized_target:
                                    # Found it!
                                    relative_path = str(file_path).replace('\\', '/')
                                    location_info = {
                                        'file': relative_path,
                                        'line': line_num,
                                        'in_impl': True,
                                        'impl_signature': impl_signature
                                    }
                                    self.source_locations_cache[module_path] = location_info
                                    return location_info
                except Exception:
                    continue
        
        return None
    
    def _find_impl_block_location(self, module_path, parts):
        """Find the source location of an impl block.
        Format: lib::module::path::impl Trait for Type
        or: lib::module::path::impl<...> Trait for Type
        """
        impl_signature = parts[-1]  # e.g., "impl AnyFrameMeta for MetaSlotStorage"
        module_parts = parts[:-1]   # Module path
        
        # Debug: log what we're searching for
        debug = False  # Set to True for debugging
        
        # Extract type name from impl signature
        # Pattern: impl [<generics>] [Trait] for TypeName
        # or: impl [<generics>] TypeName  (inherent impl)
        type_match = None
        if ' for ' in impl_signature:
            # Trait impl: impl Trait for TypeName
            type_match = re.search(r'\s+for\s+([A-Za-z_][A-Za-z0-9_<>]*)', impl_signature)
        else:
            # Inherent impl: impl TypeName
            type_match = re.search(r'impl(?:<[^>]+>)?\s+([A-Za-z_][A-Za-z0-9_<>]*)', impl_signature)
        
        if not type_match:
            if debug:
                print(f"DEBUG: Could not extract type name from impl signature: {impl_signature}")
            return None
        
        type_name = type_match.group(1).split('<')[0]  # Remove generics
        
        # Build file path
        base_paths = [Path('vostd') / 'src']
        for base_path in base_paths:
            file_path = base_path / Path(*module_parts).with_suffix('.rs')
            if file_path.exists():
                try:
                    with open(file_path, 'r', encoding='utf-8') as f:
                        lines = f.readlines()
                    
                    # Search for the impl block
                    for line_num, line in enumerate(lines, 1):
                        stripped = line.strip()
                        
                        # Match impl blocks
                        if stripped.startswith('impl'):
                            # Extract the impl signature from this line
                            current_sig = self._extract_impl_signature(stripped)
                            if current_sig:
                                # Normalize both signatures for comparison (remove extra spaces)
                                normalized_current = ' '.join(current_sig.split())
                                normalized_target = ' '.join(impl_signature.split())
                                
                                if normalized_current == normalized_target:
                                    # Found it!
                                    relative_path = str(file_path).replace('\\', '/')
                                    location_info = {
                                        'file': relative_path,
                                        'line': line_num,
                                        'in_impl': True,
                                        'impl_signature': impl_signature
                                    }
                                    self.source_locations_cache[module_path] = location_info
                                    return location_info
                except Exception as e:
                    if debug:
                        print(f"DEBUG: Exception reading {file_path}: {e}")
                    continue
        
        if debug:
            print(f"DEBUG: Could not find impl block for: {impl_signature} in module {module_parts}")
        return None
    
    def _find_impl_block_start(self, lines, current_line_idx):
        """Find the start line of an impl block that contains the given line.
        Returns dict with 'line' (0-based index), 'signature', and 'is_trait_impl', or None if not in an impl block."""
        # Simple approach: search backwards for an 'impl' line
        # Stop when we find a closing brace at the same or lower indentation level
        
        current_indent = len(lines[current_line_idx]) - len(lines[current_line_idx].lstrip())
        
        for i in range(current_line_idx - 1, -1, -1):
            line = lines[i]
            stripped = line.strip()
            
            # Skip empty lines and comments
            if not stripped or stripped.startswith('//'):
                continue
            
            line_indent = len(line) - len(line.lstrip())
            
            # If we find a closing brace at same or lower indentation, we've left the block
            if stripped.startswith('}') and line_indent <= current_indent - 4:  # assuming 4-space indent
                return None
            
            # If we find an impl line
            if stripped.startswith('impl'):
                # Extract the impl signature
                signature = self._extract_impl_signature(stripped)
                # Check if it's a trait impl (contains ' for ')
                is_trait_impl = ' for ' in stripped
                return {
                    'line': i,
                    'signature': signature,
                    'is_trait_impl': is_trait_impl
                }
        
        return None
    
    def _extract_impl_signature(self, impl_line):
        """Extract the complete impl signature from an impl line, preserving generics.
        Examples:
        - 'impl<M: AnyFrameMeta + Repr<MetaSlot>> OwnerOf for Link<M> {' 
          -> 'impl<M: AnyFrameMeta + Repr<MetaSlot>> OwnerOf for Link<M>'
        - 'impl<T> MyType<T> {' -> 'impl<T> MyType<T>'
        """
        # Simply remove the trailing '{' and any whitespace
        impl_line = impl_line.strip()
        if impl_line.endswith('{'):
            impl_line = impl_line[:-1].strip()
        
        return impl_line

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
    
    # Deduplicate based on file location and display text
    seen = set()
    unique_deps = []
    
    for dep in dependencies:
        # Check if this is an impl block with @ separator
        if '@' in dep:
            # Extract impl signature for display
            impl_sig = dep.split('@')[1]
            display_text = impl_sig
        else:
            display_text = dep
        
        # Find source location
        location = extractor.find_source_location(dep)
        
        if location:
            if location.get('in_impl'):
                # Use impl signature from location
                key = (location['file'], location['line'], location['impl_signature'])
                display_text = location['impl_signature']
            else:
                key = (location['file'], location['line'], dep)
        else:
            key = ('not_found', 0, display_text)
        
        if key not in seen:
            seen.add(key)
            unique_deps.append((location, display_text))
    
    # Output unique dependencies
    for location, display_text in unique_deps:
        if location:
            print(f"[{location['file']}:{location['line']}]  {display_text}")
        else:
            print(f"[location not found]  {display_text}")
    
    print(f"\nTotal: {len(unique_deps)} unique dependencies found (from {len(dependencies)} total)")

if __name__ == '__main__':
    main()
