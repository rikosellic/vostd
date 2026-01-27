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
import tomllib
import networkx as nx
from collections import defaultdict, deque
from pathlib import Path

ROOT = os.path.abspath(os.path.dirname(__file__))
VERUS_LOG_DIR = os.path.join(ROOT, ".verus-log")
MAPPING_CACHE_FILE = os.path.join(VERUS_LOG_DIR, "mappings_cache.pkl")
CALL_GRAPH_CACHE_FILE = os.path.join(VERUS_LOG_DIR, "call_graph_cache.pkl")

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
        
class CallGraphAnalyzer:
    """Analyzer for call graph DOT files"""
    
    def __init__(self):
        self.graph = None
        self.label_to_node_id = {}  # label -> node_id mapping
        self.node_id_to_label = {}  # node_id -> label mapping
        
    def save_call_graph_cache(self, dot_file_path):
        """Save call graph data to cache file"""
        try:
            cache_data = {
                'graph': self.graph,
                'label_to_node_id': self.label_to_node_id,
                'node_id_to_label': self.node_id_to_label,
                'dot_file_path': dot_file_path
            }
            
            os.makedirs(os.path.dirname(CALL_GRAPH_CACHE_FILE), exist_ok=True)
            with open(CALL_GRAPH_CACHE_FILE, 'wb') as f:
                pickle.dump(cache_data, f)
        except Exception as e:
            print(f"ERROR: ailed to save call graph cache: {e}")
    
    def load_call_graph_cache(self, dot_file_path):
        """Load call graph data from cache file. Returns True if successful, False otherwise"""
        try:
            if not os.path.exists(CALL_GRAPH_CACHE_FILE):
                return False
            
            with open(CALL_GRAPH_CACHE_FILE, 'rb') as f:
                cache_data = pickle.load(f)
            
            # Verify cache is for the same DOT file
            if cache_data.get('dot_file_path') != dot_file_path:
                return False
            
            # Load all data
            self.graph = cache_data['graph']
            self.label_to_node_id = cache_data['label_to_node_id']
            self.node_id_to_label = cache_data['node_id_to_label']
            
            if self.graph:
                return True
            else:
                return False
            
        except Exception as e:
            print(f"ERROR: Failed to load call graph cache: {e}")
            return False
    
    def _is_call_graph_cache_valid(self, dot_file_path):
        """Check if cache is newer than the DOT file"""
        try:
            if not os.path.exists(CALL_GRAPH_CACHE_FILE) or not os.path.exists(dot_file_path):
                return False
            
            cache_mtime = os.path.getmtime(CALL_GRAPH_CACHE_FILE)
            dot_mtime = os.path.getmtime(dot_file_path)
            
            return cache_mtime >= dot_mtime
        except Exception:
            return False
        
    def load_dot_file(self, dot_file_path):
        """Load and parse DOT file using NetworkX with caching"""
        # Try to load from cache first if cache is valid
        if self._is_call_graph_cache_valid(dot_file_path) and self.load_call_graph_cache(dot_file_path):
            return True
        
        try:
            from networkx.drawing.nx_pydot import read_dot
            
            # Read DOT file
            self.graph = read_dot(dot_file_path)
            
            # Build label mappings
            self.label_to_node_id = {}
            self.node_id_to_label = {}
            
            for node_id, attrs in self.graph.nodes(data=True):
                if 'label' in attrs:
                    label = attrs['label']
                    # Clean the label - remove quotes and escape sequences
                    clean_label = label.strip('"').replace('\\n', '\n')
                    
                    self.label_to_node_id[clean_label] = node_id
                    self.node_id_to_label[node_id] = clean_label
            
            print(f"Loaded call graph with {len(self.graph.nodes)} nodes and {len(self.graph.edges)} edges")
            
            # Save to cache after successful loading
            self.save_call_graph_cache(dot_file_path)

            return True
            
        except Exception as e:
            print(f"Error loading DOT file {dot_file_path}: {e}")
            return False
    
    def get_all_dependencies_recursive(self, target_label):
        """Get all dependencies recursively (transitive closure)"""
        if not self.graph:
            print("No call graph loaded")
            return []
            
        if target_label not in self.label_to_node_id:
            print(f"Label not found: {target_label}")
            return []
        
        node_id = self.label_to_node_id[target_label]
        
        # Use NetworkX's built-in descendants method for efficient dependency analysis
        try:
            descendant_node_ids = nx.descendants(self.graph, node_id)
            dependencies = []
            
            for desc_node_id in descendant_node_ids:
                if desc_node_id in self.node_id_to_label:
                    dep_label = self.node_id_to_label[desc_node_id]
                    dependencies.append(dep_label)
            
            return dependencies
            
        except nx.NetworkXError as e:
            print(f"Error analyzing dependencies: {e}")
            return []
    
    def get_statistics(self):
        """Get basic statistics about the call graph"""
        if not self.graph:
            return None
            
        return {
            'total_nodes': len(self.graph.nodes),
            'total_edges': len(self.graph.edges),
            'labels_mapped': len(self.label_to_node_id)
        }
        
class DependencyExtractor:
    """Main dependency extraction orchestrator"""
    
    def __init__(self):
        self.analyzer = VIRAnalyzer()
        self.call_graph = CallGraphAnalyzer()
        
    def load_call_graph(self, dot_file_path=None):
        """Load call graph from DOT file"""
        if dot_file_path is None:
            project_name = get_project_name()
            project_dir = os.path.join(VERUS_LOG_DIR, project_name)
            dot_file_path = os.path.join(project_dir, "crate-call-graph-nostd-initial.dot")
        
        if not os.path.exists(dot_file_path):
            print(f"ERROR: DOT file not found: {dot_file_path}")
            return False
            
        return self.call_graph.load_dot_file(dot_file_path)

    def preprocess(self):
        """Preprocess VIR files in the project to build complete type mappings, trait definitions, and function definitions"""     
        # The `crate.vir` file contains all definitions
        project_name = get_project_name()
        project_dir = os.path.join(VERUS_LOG_DIR, project_name)
        
        if not os.path.exists(project_dir):
            print(f"ERROR: VIR directory {project_dir} does not exist")
            return
        
        # Check for the consolidated crate.vir file
        crate_vir_path = os.path.join(project_dir, "crate.vir")
        if not os.path.exists(crate_vir_path):
            print(f"ERROR: crate.vir not found at {crate_vir_path}")
            return
        
        # Try to load from cache first if cache is valid
        if self.analyzer._is_cache_valid(crate_vir_path) and self.analyzer.load_mappings_cache():
            return
               
        # Analyze the consolidated crate.vir file
        self.analyzer.analyze_vir_file(crate_vir_path)
        
        # Save mappings to cache after analysis
        self.analyzer.save_mappings_cache()

class VIRAnalyzer:
    """Analyzer for VIR file structure"""
    
    def __init__(self):
        self.vir_path_to_function_info = {}  # vir_path -> {rust_path, vir_location, source_location}
        self.vir_path_to_datatype_info = {}  # vir_path -> {rust_path, vir_location, source_location}
        
        # 反向映射用于call graph分析
        self.function_rust_path_to_info = {}  # rust_path -> {vir_path, call_graph_node_name, ...}
        self.function_call_graph_name_to_vir_path = {}  # call_graph_node_name -> vir_path
        
        self.source_analyzer = SourceCodeAnalyzer()

    def save_mappings_cache(self):
        """Save all mappings to cache file"""
        try:
            cache_data = {
                'vir_path_to_function_info': self.vir_path_to_function_info,
                'vir_path_to_datatype_info': self.vir_path_to_datatype_info,
                'function_rust_path_to_info': self.function_rust_path_to_info,
                'function_call_graph_name_to_vir_path': self.function_call_graph_name_to_vir_path
            }
            
            os.makedirs(os.path.dirname(MAPPING_CACHE_FILE), exist_ok=True)
            with open(MAPPING_CACHE_FILE, 'wb') as f:
                pickle.dump(cache_data, f)
        except Exception as e:
            print(f"ERROR：Failed to save mappings cache: {e}")
    
    def load_mappings_cache(self):
        """Load all mappings from cache file. Returns True if successful, False otherwise"""
        try:
            if not os.path.exists(MAPPING_CACHE_FILE):
                return False
            
            with open(MAPPING_CACHE_FILE, 'rb') as f:
                cache_data = pickle.load(f)
            
            # Verify all required mappings are present
            required_keys = ['vir_path_to_function_info', 'vir_path_to_datatype_info', 
                           'function_rust_path_to_info', 'function_call_graph_name_to_vir_path']
            
            for key in required_keys:
                if key not in cache_data:
                    return False
            
            # Load all mappings
            self.vir_path_to_function_info = cache_data['vir_path_to_function_info']
            self.vir_path_to_datatype_info = cache_data['vir_path_to_datatype_info']
            self.function_rust_path_to_info = cache_data['function_rust_path_to_info']
            self.function_call_graph_name_to_vir_path = cache_data['function_call_graph_name_to_vir_path']
        
            return True
            
        except Exception as e:
            return False
    
    def _is_cache_valid(self, vir_file_path):
        """Check if cache is newer than the VIR file"""
        try:
            if not os.path.exists(MAPPING_CACHE_FILE) or not os.path.exists(vir_file_path):
                return False
            
            cache_mtime = os.path.getmtime(MAPPING_CACHE_FILE)
            vir_mtime = os.path.getmtime(vir_file_path)
            
            return cache_mtime >= vir_mtime
        except Exception:
            return False

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
        
        if func_path and not func_path.startswith('vstd!'):
            rust_path = self._extract_rust_path_from_vir_path(func_path)
            # 检查是否是impl方法，如果是则替换为实际类型
            resolved_rust_path = self._resolve_impl_path(rust_path, source_location)
            
            function_info = {
                'rust_path': resolved_rust_path,
                'vir_location': self._extract_vir_location(file_path, vir_line),
                'is_impl': 'impl&%' in func_path,  # Check if it's a trait method
            }
            
            # Add source location if available
            if source_location:
                function_info['source_location'] = source_location
            
            self.vir_path_to_function_info[func_path] = function_info
            
            # 构建反向映射
            self._build_reverse_mappings(func_path, resolved_rust_path)

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
        
        if datatype_path and not datatype_path.startswith('vstd!'):
            rust_path = self._extract_rust_path_from_vir_path(datatype_path)
            datatype_info = {
                'rust_path': rust_path,
                'vir_location': self._extract_vir_location(file_path, vir_line),
            }
            
            # Add source location if available
            if source_location:
                datatype_info['source_location'] = source_location
            
            self.vir_path_to_datatype_info[datatype_path] = datatype_info

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
    
    def _resolve_impl_path(self, rust_path, source_location):
        """Replace impl&%N with actual type name from source code"""
        if 'impl&%' not in rust_path or not source_location:
            return rust_path
        
        try:
            # 从 source_location 中提取文件路径 (处理Windows路径)
            # 格式: D:\path\file.rs:line
            import re
            # 使用正则表达式匹配文件路径，处理Windows驱动器路径
            path_match = re.match(r'^(.+\.(rs|vir)):\d+$', source_location)
            if not path_match:
                return rust_path
            source_file = path_match.group(1)
            
            # 从 rust_path 中提取 impl&%N 部分
            impl_match = re.search(r'impl&%([0-9]+)', rust_path)
            if not impl_match:
                return rust_path
            
            impl_index = int(impl_match.group(1))
            
            # 使用 SourceCodeAnalyzer 分析源文件
            mappings = self.source_analyzer.analyze_source_file(source_file)
            
            if impl_index in mappings:
                type_name = mappings[impl_index]
                # 替换 impl&%N 为实际类型名
                resolved_path = re.sub(r'impl&%[0-9]+', type_name, rust_path)
                return resolved_path
            
        except (ValueError, IndexError, FileNotFoundError):
            pass
        
        return rust_path
    
    def _build_reverse_mappings(self, vir_path, rust_path):
        """构建反向映射：rust_path -> info 和 call_graph_node_name -> vir_path"""
        # 生成 call graph 节点名称格式（使用::分隔符，基于vir_path保留impl&%形式）
        vir_rust_path = self._extract_rust_path_from_vir_path(vir_path)
        call_graph_node_name = self._rust_path_to_call_graph_name(vir_rust_path)
        
        # 构建 rust_path -> info 映射
        self.function_rust_path_to_info[rust_path] = {
            'vir_path': vir_path,
            'call_graph_node_name': call_graph_node_name,
        }
        
        # 构建 call_graph_node_name -> vir_path 映射
        self.function_call_graph_name_to_vir_path[call_graph_node_name] = vir_path
    
    def _rust_path_to_call_graph_name(self, rust_path):
        """将rust_path格式转换为call graph中使用的::格式
        例如: lib.lock_protocol_rcu.spec.utils.get_child -> lib::lock_protocol_rcu::spec::utils::get_child
        """
        if rust_path:
            return rust_path.replace('.', '::')
        return rust_path
    
    def get_function_by_rust_path(self, rust_path):
        """根据rust_path获取函数信息"""
        return self.function_rust_path_to_info.get(rust_path)
    
    def get_function_by_call_graph_name(self, call_graph_name):
        """根据call_graph节点名称获取vir_path"""
        return self.function_call_graph_name_to_vir_path.get(call_graph_name)
    
    def get_all_reverse_mappings_info(self):
        """获取反向映射的统计信息"""
        return {
            'rust_path_mappings': len(self.function_rust_path_to_info),
            'call_graph_mappings': len(self.function_call_graph_name_to_vir_path),
            'total_functions': len(self.vir_path_to_function_info)
        }
    
def test_function_info():
    extractor = DependencyExtractor()
    extractor.analyzer.analyze_vir_file("D:\\Projects\\VerusProjects\\vostd\\.verus-log\\cortenmm\\lock_protocol_rcu__spec__utils-poly.vir")
    #extractor.analyzer.analyze_vir_file("D:\\Projects\\VerusProjects\\vostd\\.verus-log\\cortenmm\\lock_protocol_rcu__spec__common-poly.vir")
    
    print("=== 示例函数信息 ===")
    for i in range(3):
        if extractor.analyzer.vir_path_to_function_info:
            example_key = list(extractor.analyzer.vir_path_to_function_info.keys())[i]
            print(f"VIR名称: {example_key}")
            print(f"详细信息: {extractor.analyzer.vir_path_to_function_info[example_key]}")
            print()
    
    print(f"\n总数: {len(extractor.analyzer.vir_path_to_function_info)}")
    
    print("\n=== 反向映射信息 ===")
    mapping_info = extractor.analyzer.get_all_reverse_mappings_info()
    print(f"反向映射统计: {mapping_info}")
    
    print("\n=== 反向映射示例 ===")
    # 测试按rust_path查找
    if extractor.analyzer.function_rust_path_to_info:
        example_rust_path = list(extractor.analyzer.function_rust_path_to_info.keys())[0]
        print(f"Rust路径: {example_rust_path}")
        print(f"映射信息: {extractor.analyzer.get_function_by_rust_path(example_rust_path)}")
        
        # 测试按call_graph_name查找
        call_graph_name = extractor.analyzer.function_rust_path_to_info[example_rust_path]['call_graph_node_name']
        vir_path = extractor.analyzer.get_function_by_call_graph_name(call_graph_name)
        print(f"Call Graph名称: {call_graph_name}")
        print(f"对应VIR路径: {vir_path}")
        print()

def test_datatype_info():
    extractor = DependencyExtractor()
    extractor.analyzer.analyze_vir_file("D:\\Projects\\VerusProjects\\vostd\\.verus-log\\cortenmm\\lock_protocol_rcu__mm__page_table__cursor-poly.vir")
    # extractor.analyzer.analyze_vir_file("D:\\Projects\\VerusProjects\\vostd\\.verus-log\\cortenmm\\lock_protocol_rcu__spec__common-poly.vir")
    # extractor.preprocess()

    print("=== 示例数据类型信息 ===")
    for i in range(3):
        if extractor.analyzer.vir_path_to_datatype_info:
            example_key = list(extractor.analyzer.vir_path_to_datatype_info.keys())[i]
            print(f"VIR名称: {example_key}")
            print(f"详细信息: {extractor.analyzer.vir_path_to_datatype_info[example_key]}")
            print()
    
    print(f"\n总数: {len(extractor.analyzer.vir_path_to_datatype_info)}")

def test_full():
    extractor = DependencyExtractor()
    extractor.preprocess()
    
    print("=== 示例函数信息 ===")
    for i in range(3):
        if extractor.analyzer.vir_path_to_function_info:
            example_key = list(extractor.analyzer.vir_path_to_function_info.keys())[i]
            print(f"VIR名称: {example_key}")
            print(f"详细信息: {extractor.analyzer.vir_path_to_function_info[example_key]}")
            print()
    
    print(f"\n总数: {len(extractor.analyzer.vir_path_to_function_info)}")
    
    print("\n=== 反向映射信息 ===")
    mapping_info = extractor.analyzer.get_all_reverse_mappings_info()
    print(f"反向映射统计: {mapping_info}")
    
    print("\n=== 反向映射示例 ===")
    # 测试按rust_path查找
    if extractor.analyzer.function_rust_path_to_info:
        example_rust_path = list(extractor.analyzer.function_rust_path_to_info.keys())[0]
        print(f"Rust路径: {example_rust_path}")
        print(f"映射信息: {extractor.analyzer.get_function_by_rust_path(example_rust_path)}")
        
        # 测试按call_graph_name查找
        call_graph_name = extractor.analyzer.function_rust_path_to_info[example_rust_path]['call_graph_node_name']
        vir_path = extractor.analyzer.get_function_by_call_graph_name(call_graph_name)
        print(f"Call Graph名称: {call_graph_name}")
        print(f"对应VIR路径: {vir_path}")
        print()

def test_call_graph():
    """Test call graph analysis functionality"""
    extractor = DependencyExtractor()
    
    # Load call graph
    print("=== 加载调用图 ===")
    if extractor.load_call_graph():
        stats = extractor.call_graph.get_statistics()
        print(f"调用图统计: {stats}")
    else:
        print("无法加载调用图")
        return
    
    
    # Test dependency analysis
    print("=== 依赖分析测试 ===")

    test_function = "Fun\nlib::lock_protocol_rcu::spec::utils::impl&%0::get_child"
    print(f"分析函数: {test_function}")
    
    # Get all dependencies (recursive)
    all_deps = extractor.call_graph.get_all_dependencies_recursive(test_function)
    print(f"所有依赖 ({len(all_deps)} 个):")
    for i, dep in enumerate(all_deps[:]): 
        print(f"  {i+1}. {dep}")

def main():
    """Main entry point for the dependency extractor"""
    pass

if __name__ == '__main__':
    #test_datatype_info()
    #test_function_info()
    #test_full()
    test_call_graph()