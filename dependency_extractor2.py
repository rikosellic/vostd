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
import pickle
try:
    import tomllib  # Python 3.11+
except ImportError:
    try:
        import toml as tomllib  # fallback
    except ImportError:
        tomllib = None
from collections import defaultdict, deque
from pathlib import Path

ROOT = os.path.abspath(os.path.dirname(__file__))
VERUS_LOG_DIR = os.path.join(ROOT, ".verus-log")
TRAIT_CACHE_FILE = os.path.join(VERUS_LOG_DIR, "trait_cache.pkl")

def get_project_name():
    """Get the first member from workspace Cargo.toml as project name."""
    if tomllib is None:
        return 'vostd'  # fallback if no toml library
    try:
        with open('Cargo.toml', 'rb' if hasattr(tomllib, 'load') and 'b' in tomllib.load.__doc__ else 'r') as f:
            if hasattr(tomllib, 'load'):
                cargo_config = tomllib.load(f)
            else:
                cargo_config = tomllib.loads(f.read())
        members = cargo_config.get('workspace', {}).get('members', [])
        if members:
            return members[0]
    except (FileNotFoundError, Exception):
        pass
    return 'vostd'  # fallback to default

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
        
class DependencyExtractor:
    """Main dependency extraction orchestrator"""
    
    def __init__(self):
        self.analyzer = VIRAnalyzer()

    def preprocess(self):
        """Preprocess ALL VIR files in the project to build complete type mappings, trait definitions, and function definitions
        
        Args:
            test_file: If specified, only process this single VIR file instead of all files
        """     
        # Get all VIR files in the project
        project_name = get_project_name()
        project_dir = os.path.join(VERUS_LOG_DIR, project_name)
        
        if not os.path.exists(project_dir):
            print(f"ERROR: VIR directory {project_dir} does not exist")
            return
        
        # Scan for VIR files
        all_vir_files = []
        for file_name in os.listdir(project_dir):
            if file_name.endswith('-poly.vir'):
                file_path = os.path.join(project_dir, file_name)
                all_vir_files.append(file_path)
        
        # Analyze all VIR files to build complete database
        for vir_file in all_vir_files:
            self.analyzer.analyze_vir_file(vir_file)

class VIRAnalyzer:
    """Analyzer for VIR file structure"""
    
    def __init__(self):
        self.function_info = {}  # vir_path -> {rust_path, vir_location, source_location}
        self.datatype_info = {}  # vir_path -> {rust_path, vir_location, source_location}

    def analyze_vir_file(self, file_path):
        """Analyze a complete VIR file"""
            
        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            # Parse the VIR file as S-expressions
            parser = SExprParser(content)
            
            # VIR files can contain multiple top-level expressions
            expressions = []
            expr_count = 0
            current_line = 1
            
            while parser.pos < parser.length:
                parser.skip_whitespace()
                if parser.pos >= parser.length:
                    break
                    
                # Count lines up to current position
                lines_before = content[:parser.pos].count('\n')
                current_line = lines_before + 1
                
                expr = parser.parse()
                if expr:
                    expressions.append((expr, current_line))
                    expr_count += 1
            
            # Extract information from all expressions
            for i, (expr, line_num) in enumerate(expressions):
                self.preprocess_function_info(expr, file_path, line_num)
                self.preprocess_datatype_info(expr, file_path, line_num)
            
            pass  # Analysis complete
            
        except Exception as e:
            print(f"Error analyzing {file_path}: {e}")

    def _extract_rust_module_from_filename(self, file_path):
        """Extract module path from VIR filename.
        Example: lock_protocol_rcu__spec__common-poly.vir -> lib::lock_protocol_rcu::spec::common
        """
        import os
        filename = os.path.basename(file_path)
        if filename.endswith('-poly.vir'):
            module_part = filename[:-9]  # Remove '-poly.vir'
            module_path = module_part.replace('__', '::')
            return f"lib::{module_path}"
        return None

    def preprocess_function_info(self, expr, file_path, vir_line=None):
        """Extract function definition from VIR expression - only top-level functions from current module"""
        if not isinstance(expr, list) or len(expr) < 2:
            return
        
        # Extract source location from @ wrapper
        source_location = self._extract_source_location(expr)
        
        # Handle @ location wrappers: ['@', 'location', ['Function', ...]]
        if expr[0] == '@' and len(expr) >= 3 and isinstance(expr[2], list) and expr[2][0] == 'Function':
            func_expr = expr[2]
        elif expr[0] == 'Function':
            func_expr = expr
        else:
            return
        
        func_path = None
        func_body = None
        
        for i in range(1, len(func_expr)):
            if func_expr[i] == ':name' and i + 1 < len(func_expr):
                if isinstance(func_expr[i + 1], list) and func_expr[i + 1][0] == 'Fun':
                    func_path = self._extract_vir_path_from_expr(func_expr[i + 1])
            elif func_expr[i] == ':body' and i + 1 < len(func_expr):
                func_body = func_expr[i + 1]
        
        if func_path:
            rust_path = self._extract_rust_path_from_vir_path(func_path)
            if rust_path:
                # Extract module name from file name and filter functions
                module_name = self._extract_rust_module_from_filename(file_path)
                if module_name and rust_path.startswith(module_name):
                    function_info = {
                        'rust_path': rust_path,
                        'vir_location': self._extract_vir_location(file_path, vir_line),
                        'is_impl': 'impl&%' in func_path,  # Check if it's a trait method
                    }
                    
                    # Add source location if available
                    if source_location:
                        function_info['source_location'] = source_location
                    
                    self.function_info[func_path] = function_info

    def preprocess_datatype_info(self, expr, file_path, vir_line=None):
        """Extract datatype definition from VIR expression - only top-level datatypes from current module"""
        """Type Alias is not handled"""
        if not isinstance(expr, list) or len(expr) < 2:
            return
        
        # Extract source location from @ wrapper
        source_location = self._extract_source_location(expr)
        
        # Handle @ location wrappers: ['@', 'location', ['Datatype', ...]]
        if expr[0] == '@' and len(expr) >= 3 and isinstance(expr[2], list) and expr[2][0] == 'Datatype':
            datatype_expr = expr[2]
        elif expr[0] == 'Datatype':
            datatype_expr = expr
        else:
            return
        
        datatype_path = None
        variants = None
        
        # Extract the datatype path and variants
        i = 1
        while i < len(datatype_expr):
            if datatype_expr[i] == ':name' and i + 1 < len(datatype_expr):
                # Extract path from (Dt Path "lib!...")
                name_expr = datatype_expr[i + 1]
                if isinstance(name_expr, list) and len(name_expr) >= 3:
                    if name_expr[0] == 'Dt' and name_expr[1] == 'Path':
                        raw_path = name_expr[2]
                        datatype_path = raw_path
                i += 2
            elif datatype_expr[i] == ':variants' and i + 1 < len(datatype_expr):
                variants = datatype_expr[i + 1]
                i += 2
            else:
                i += 1
        
        if datatype_path:
            rust_path = self._extract_rust_path_from_vir_path(datatype_path)
            if rust_path:
                # Extract module name from file name and filter datatypes
                module_name = self._extract_rust_module_from_filename(file_path)
                if module_name and rust_path.startswith(module_name):
                    datatype_info = {
                        'rust_path': rust_path,
                        'vir_location': self._extract_vir_location(file_path, vir_line),
                    }
                    
                    # Add source location if available
                    if source_location:
                        datatype_info['source_location'] = source_location
                    
                    self.datatype_info[datatype_path] = datatype_info

    def _extract_rust_path_from_vir_path(self, path):
        """Convert VIR path format to Rust format"""
        if not path or not path.startswith('lib!'):
            return None
        clean = path[4:].replace('.', '::').rstrip(':').rstrip('::')
        return f"lib::{clean}" if clean else None
    
    def _extract_vir_path_from_expr(self, expr):
        """Extract path string from VIR path expression"""
        if isinstance(expr, list):
            for item in expr:
                if isinstance(item, str) and 'lib!' in item:
                    return item
        return None
    
    def _extract_source_location(self, expr):
        """Extract source file and line number in VSCode format: file.rs:123
        Format: "file_path:start_line:start_col: end_line:end_col (#0)"
        """
        if isinstance(expr, list) and len(expr) >= 2 and expr[0] == '@':
            location_str = expr[1]
            if isinstance(location_str, str):
                # Parse format: "D:\path\file.rs:291:5: 291:67 (#0)"
                try:
                    # Find the last occurrence of '.rs:' to handle Windows paths with colons
                    rs_idx = location_str.rfind('.rs:')
                    if rs_idx != -1:
                        file_path = location_str[:rs_idx + 3]  # Include '.rs'
                        rest = location_str[rs_idx + 4:]  # After '.rs:'
                        
                        # Get the first line number
                        start_line = int(rest.split(':')[0])
                        
                        return f"{file_path}:{start_line}"
                except (ValueError, IndexError):
                    pass
        return None
    
    def _extract_vir_location(self, file_path, current_line=None):
        """Extract VIR file location in VSCode format: file.vir:line
        """
        if current_line is not None:
            return f"{file_path}:{current_line}"
        else:
            return file_path
    
def test_function_info():
    extractor = DependencyExtractor()
    #extractor.analyzer.analyze_vir_file("D:\\Projects\\VerusProjects\\vostd\\.verus-log\\cortenmm\\lock_protocol_rcu__spec__utils-poly.vir")
    extractor.analyzer.analyze_vir_file("D:\\Projects\\VerusProjects\\vostd\\.verus-log\\cortenmm\\lock_protocol_rcu__spec__common-poly.vir")
    
    print("=== 示例函数信息 ===")
    for i in range(3):
        if extractor.analyzer.function_info:
            example_key = list(extractor.analyzer.function_info.keys())[i]
            print(f"VIR名称: {example_key}")
            print(f"详细信息: {extractor.analyzer.function_info[example_key]}")
            print()
    
    print(f"\n总数: {len(extractor.analyzer.function_info)}")

def test_datatype_info():
    extractor = DependencyExtractor()
    extractor.analyzer.analyze_vir_file("D:\\Projects\\VerusProjects\\vostd\\.verus-log\\cortenmm\\lock_protocol_rcu__mm__page_table__cursor-poly.vir")
    #extractor.analyzer.analyze_vir_file("D:\\Projects\\VerusProjects\\vostd\\.verus-log\\cortenmm\\lock_protocol_rcu__spec__common-poly.vir")
    
    print("=== 示例数据类型信息 ===")
    for i in range(3):
        if extractor.analyzer.datatype_info:
            example_key = list(extractor.analyzer.datatype_info.keys())[i]
            print(f"VIR名称: {example_key}")
            print(f"详细信息: {extractor.analyzer.datatype_info[example_key]}")
            print()
    
    print(f"\n总数: {len(extractor.analyzer.datatype_info)}")

if __name__ == '__main__':
    test_datatype_info()
    #test_function_info()