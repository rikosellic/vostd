#!/usr/bin/env python3
"""
依赖关系提取器
从Verus验证日志中提取给定函数的所有依赖项
"""

import os
import re
import sys
from pathlib import Path
from typing import Set, Dict, List, Tuple
from collections import defaultdict


class DependencyExtractor:
    def __init__(self, verus_log_dir: str = ".verus-log"):
        self.verus_log_dir = Path(verus_log_dir)
        self.crate_files: Dict[str, List[Path]] = {}
        self.dependencies: Set[str] = set()
        self.global_path_mapping: Dict[str, str] = {}  # 全局路径到crate的映射
        
        # 扫描所有crate的验证文件
        self._scan_crate_files()
        # 建立全局路径映射
        self._build_global_path_mapping()
    
    def _scan_crate_files(self):
        """扫描.verus-log目录下所有crate的poly.vir文件"""
        if not self.verus_log_dir.exists():
            print(f"错误：目录 {self.verus_log_dir} 不存在")
            return
        
        for crate_dir in self.verus_log_dir.iterdir():
            if crate_dir.is_dir():
                crate_name = crate_dir.name
                vir_files = list(crate_dir.glob("*-poly.vir"))
                self.crate_files[crate_name] = vir_files
                print(f"发现 crate: {crate_name}, {len(vir_files)} 个验证文件", file=sys.stderr)
    
    def _build_global_path_mapping(self):
        """扫描所有VIR文件，建立全局的路径到crate映射"""
        print("\n构建全局路径映射...", file=sys.stderr)
        
        for crate_name, vir_files in self.crate_files.items():
            for vir_file in vir_files:
                try:
                    with open(vir_file, 'r', encoding='utf-8', errors='ignore') as f:
                        content = f.read()
                    
                    # 提取所有带注释的定义（Datatype, Function, Trait等）
                    annotation_pattern = r'\(@\s+"([^"]+):\d+:\d+:\s+\d+:\d+\s+\(#\d+\)"[^)]*\((?:Datatype|Function|Trait)[^)]*:name[^)]*Path\s+"([^"]+)"'
                    for match in re.finditer(annotation_pattern, content, re.MULTILINE):
                        file_path = match.group(1)
                        item_path = match.group(2)
                        
                        real_crate = self._extract_source_file_crate(file_path)
                        if real_crate and item_path.startswith("lib!"):
                            clean_path = item_path[4:].rstrip('.')
                            # 记录完整路径的所有前缀
                            parts = clean_path.split('.')
                            for i in range(1, len(parts) + 1):
                                prefix = '.'.join(parts[:i])
                                # 只在还没有映射的情况下添加，或者更新为更精确的映射
                                if prefix not in self.global_path_mapping:
                                    self.global_path_mapping[prefix] = real_crate
                    
                    # 还要捕获独立的trait定义行，如：(trait "lib!ownership.Inv.")
                    # 但只在这个文件是该模块的定义文件时才添加
                    # 通过检查vir文件名来判断
                    file_module = vir_file.stem.replace('-poly', '').replace('__', '.')
                    
                    trait_def_pattern = r'\(trait\s+"([^"]+)"\)'
                    for match in re.finditer(trait_def_pattern, content):
                        trait_path = match.group(1)
                        if trait_path.startswith("lib!"):
                            clean_path = trait_path[4:].rstrip('.')
                            # 只有当trait的路径与文件模块路径匹配时才添加映射
                            # 例如：ownership.Inv 应该在 ownership-poly.vir文件中
                            if clean_path.startswith(file_module):
                                parts = clean_path.split('.')
                                for i in range(1, len(parts) + 1):
                                    prefix = '.'.join(parts[:i])
                                    if prefix not in self.global_path_mapping:
                                        self.global_path_mapping[prefix] = crate_name
                
                except Exception as e:
                    pass  # 忽略错误，继续处理其他文件
        
        print(f"全局路径映射构建完成，共 {len(self.global_path_mapping)} 条映射", file=sys.stderr)
    
    def _normalize_path(self, path: str, source_crate: str) -> str:
        """
        将验证文件中的路径标准化为跨crate的完整路径
        
        参数:
            path: 验证文件中的路径（如 "lib!mm.frame.linked_list.LinkedList."）
            source_crate: 该路径所在的源crate名称
        
        返回:
            标准化的路径（如 "aster_common::mm::frame::linked_list::LinkedList"）
        """
        # 移除尾部的点
        path = path.rstrip('.')
        
        # 处理lib!前缀 - lib代表当前crate
        if path.startswith("lib!"):
            path = path[4:]  # 移除 "lib!"
            # 将点号替换为::
            path = path.replace('.', '::')
            # 添加crate名称前缀
            return f"{source_crate}::{path}"
        
        # 处理其他已知的crate（如vstd, core等）
        crate_mapping = {
            'vstd': 'vstd',
            'core': 'core',
            'alloc': 'alloc',
            'std': 'std',
        }
        
        for prefix, crate_name in crate_mapping.items():
            if path.startswith(f"{prefix}!"):
                path = path[len(prefix)+1:]  # 移除前缀和!
                path = path.replace('.', '::')
                return f"{crate_name}::{path}"
        
        # 直接将点号替换为::
        return path.replace('.', '::')
    
    def _normalize_path_with_mapping(self, path: str, source_crate: str, path_to_crate: Dict[str, str]) -> str:
        """
        使用路径映射将验证文件中的路径标准化为跨crate的完整路径
        
        参数:
            path: 验证文件中的路径（如 "lib!mm.frame.linked_list.LinkedList."）
            source_crate: 该路径所在文件的crate名称
            path_to_crate: 路径到真实crate的映射
        
        返回:
            标准化的路径，如果应该过滤则返回None
        """
        # 移除尾部的点
        path = path.rstrip('.')
        
        # 过滤掉匿名impl块
        if 'impl&%' in path or 'anonymous_closure' in path or 'verus_builtin' in path:
            return None
        
        # 处理lib!前缀
        if path.startswith("lib!"):
            clean_path = path[4:]  # 移除 "lib!"
            
            # 查找真实的crate（先从全局映射查找，使用最长匹配）
            real_crate = None
            max_len = 0
            
            # 首先尝试从全局映射中查找
            for known_path, crate in self.global_path_mapping.items():
                if clean_path.startswith(known_path) and len(known_path) > max_len:
                    real_crate = crate
                    max_len = len(known_path)
            
            # 如果全局映射中没有找到，再从本地映射中查找
            if not real_crate:
                for known_path, crate in path_to_crate.items():
                    if clean_path.startswith(known_path) and len(known_path) > max_len:
                        real_crate = crate
                        max_len = len(known_path)
            
            if not real_crate:
                real_crate = source_crate
            
            # 将点号替换为::
            clean_path = clean_path.replace('.', '::')
            return f"{real_crate}::{clean_path}"
        
        # 处理其他已知的crate
        # 过滤标准库
        if path.startswith('vstd!') or path.startswith('core!') or path.startswith('alloc!') or path.startswith('std!'):
            return None
        
        # 直接将点号替换为::
        return path.replace('.', '::')
    
    def _extract_function_module_path(self, function_path: str) -> Tuple[str, str, str]:
        """
        从函数路径中提取crate、模块路径和函数名
        
        参数:
            function_path: 如 "ostd::src::mm::frame::linked_list::LinkedList::push_front"
        
        返回:
            (crate_name, module_path, function_name)
            如: ("ostd", "mm.frame.linked_list", "LinkedList::push_front")
        """
        parts = function_path.split("::")
        
        if len(parts) < 2:
            raise ValueError(f"无效的函数路径: {function_path}")
        
        crate_name = parts[0]
        
        # 移除 'src' 如果存在
        if len(parts) > 1 and parts[1] == 'src':
            parts = [parts[0]] + parts[2:]
        
        # 最后一个或两个部分是函数名（可能包含类型名）
        # 例如: LinkedList::push_front
        if len(parts) >= 3:
            module_parts = parts[1:-2]
            type_and_func = parts[-2:]
            module_path = '.'.join(module_parts)
            function_name = '::'.join(type_and_func)
        else:
            module_path = ""
            function_name = parts[-1]
        
        return crate_name, module_path, function_name
    
    def _find_module_file(self, crate_name: str, module_path: str) -> List[Path]:
        """
        查找包含指定模块的验证文件
        
        参数:
            crate_name: crate名称
            module_path: 模块路径，用点分隔（如 "mm.frame.linked_list"）
        
        返回:
            匹配的文件路径列表
        """
        if crate_name not in self.crate_files:
            return []
        
        # 将模块路径转换为文件名模式
        # mm.frame.linked_list -> mm__frame__linked_list
        file_pattern = module_path.replace('.', '__')
        
        matching_files = []
        for vir_file in self.crate_files[crate_name]:
            if file_pattern in vir_file.stem:
                matching_files.append(vir_file)
        
        return matching_files
    
    def _extract_source_file_crate(self, file_annotation: str) -> str:
        """
        从文件路径注释中提取真实的crate名称
        
        参数:
            file_annotation: 如 "D:\\Projects\\VerusProjects\\vostd\\vstd_extra\\src\\ownership.rs"
        
        返回:
            crate名称，如 "vstd_extra"
        """
        # 规范化路径分隔符
        path = file_annotation.replace('\\', '/')
        
        # 查找vostd后面的crate目录
        if 'vostd/' in path:
            after_vostd = path.split('vostd/', 1)[1]
            crate_name = after_vostd.split('/', 1)[0]
            # 排除src目录
            if crate_name != 'src':
                return crate_name
        
        return None
    
    def _parse_vir_file(self, vir_file: Path, source_crate: str) -> Set[str]:
        """
        解析VIR文件，提取所有依赖的类型和函数
        
        参数:
            vir_file: VIR文件路径
            source_crate: 源crate名称
        
        返回:
            依赖项集合
        """
        dependencies = set()
        path_to_crate = {}  # 记录路径到真实crate的映射
        
        try:
            with open(vir_file, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            # 首先提取所有的注释，建立路径到crate的映射
            # 匹配格式: (@ "文件路径:行:列: 行:列 (#数字)" ...)
            annotation_pattern = r'\(@\s+"([^"]+):\d+:\d+:\s+\d+:\d+\s+\(#\d+\)"[^)]*\((?:Datatype|Function|Trait)[^)]*:name[^)]*Path\s+"([^"]+)"'
            for match in re.finditer(annotation_pattern, content, re.MULTILINE):
                file_path = match.group(1)
                item_path = match.group(2)
                
                real_crate = self._extract_source_file_crate(file_path)
                if real_crate:
                    # 移除lib!前缀
                    if item_path.startswith("lib!"):
                        clean_path = item_path[4:].rstrip('.')
                        # 记录完整路径的所有前缀
                        parts = clean_path.split('.')
                        for i in range(1, len(parts) + 1):
                            prefix = '.'.join(parts[:i])
                            path_to_crate[prefix] = real_crate
            
            # 提取所有路径引用
            # 匹配格式: (Dt Path "lib!mm.frame.linked_list.LinkedList.")
            path_pattern = r'\(Dt Path "([^"]+)"\)'
            for match in re.finditer(path_pattern, content):
                path = match.group(1)
                normalized = self._normalize_path_with_mapping(path, source_crate, path_to_crate)
                if normalized:
                    dependencies.add(normalized)
            
            # 提取trait引用
            # 匹配格式: (TraitId Path "lib!cast_ptr.Repr.")
            trait_pattern = r'\(TraitId Path "([^"]+)"\)'
            for match in re.finditer(trait_pattern, content):
                path = match.group(1)
                normalized = self._normalize_path_with_mapping(path, source_crate, path_to_crate)
                if normalized:
                    dependencies.add(normalized)
            
            # 提取函数调用
            # 匹配格式: (FnDef (FunId Path "lib!mm.frame.linked_list.LinkedList.push_front.")
            fn_pattern = r'\(FunId Path "([^"]+)"\)'
            for match in re.finditer(fn_pattern, content):
                path = match.group(1)
                normalized = self._normalize_path_with_mapping(path, source_crate, path_to_crate)
                if normalized:
                    dependencies.add(normalized)
            
            # 不再提取impl引用，因为impl&%数字这种自动生成的impl块意义不大
                
        except Exception as e:
            print(f"警告：解析文件 {vir_file} 时出错: {e}", file=sys.stderr)
        
        return dependencies
    
    def extract_dependencies(self, function_path: str, max_depth: int = 5) -> Set[str]:
        """
        提取给定函数的所有依赖项
        
        参数:
            function_path: 函数的完整路径（如 "ostd::src::mm::frame::linked_list::LinkedList::push_front"）
            max_depth: 最大递归深度
        
        返回:
            所有依赖项的集合
        """
        # 解析函数路径
        crate_name, module_path, function_name = self._extract_function_module_path(function_path)
        
        print(f"\n分析函数: {function_path}", file=sys.stderr)
        print(f"  Crate: {crate_name}", file=sys.stderr)
        print(f"  模块: {module_path}", file=sys.stderr)
        print(f"  函数: {function_name}", file=sys.stderr)
        
        # 查找相关的验证文件
        module_files = self._find_module_file(crate_name, module_path)
        
        if not module_files:
            print(f"警告：未找到 {crate_name} 中模块 {module_path} 的验证文件", file=sys.stderr)
            return set()
        
        print(f"\n找到 {len(module_files)} 个相关文件:", file=sys.stderr)
        for f in module_files:
            print(f"  - {f.name}", file=sys.stderr)
        
        # 用于追踪已处理的依赖，避免重复处理
        processed = set()
        to_process = set()
        all_dependencies = set()
        
        # 首先处理主模块文件
        for vir_file in module_files:
            deps = self._parse_vir_file(vir_file, crate_name)
            all_dependencies.update(deps)
            to_process.update(deps)
        
        # 递归处理依赖
        depth = 0
        while to_process and depth < max_depth:
            depth += 1
            print(f"\n深度 {depth}: 处理 {len(to_process)} 个依赖项...", file=sys.stderr)
            
            current_batch = to_process - processed
            to_process = set()
            
            for dep in current_batch:
                processed.add(dep)
                
                # 解析依赖项的crate和模块
                dep_parts = dep.split("::")
                if len(dep_parts) < 2:
                    continue
                
                dep_crate = dep_parts[0]
                
                # 跳过标准库和外部crate（已在规范化时过滤）
                
                # 查找该依赖项的定义文件
                # 从路径中提取模块部分
                if len(dep_parts) >= 3:
                    # 假设最后一个是类型/函数名
                    dep_module = '.'.join(dep_parts[1:-1])
                    dep_files = self._find_module_file(dep_crate, dep_module)
                    
                    for vir_file in dep_files:
                        new_deps = self._parse_vir_file(vir_file, dep_crate)
                        new_deps = new_deps - processed
                        all_dependencies.update(new_deps)
                        to_process.update(new_deps)
        
        return all_dependencies
    
    def print_dependencies(self, dependencies: Set[str]):
        """打印依赖项，按crate分组"""
        # 按crate分组
        by_crate = defaultdict(set)
        for dep in dependencies:
            parts = dep.split("::", 1)
            if len(parts) == 2:
                crate, path = parts
                by_crate[crate].add(path)
            else:
                by_crate['unknown'].add(dep)
        
        # 打印结果
        print("\n" + "="*80)
        print("依赖项列表（按crate分组）")
        print("="*80)
        
        for crate in sorted(by_crate.keys()):
            print(f"\n【{crate}】")
            for path in sorted(by_crate[crate]):
                full_path = f"{crate}::{path}"
                print(f"  {full_path}")
        
        print(f"\n总计: {len(dependencies)} 个依赖项")
        print("="*80)


def main():
    if len(sys.argv) < 2:
        print("用法: python dependency_extractor.py <函数路径> [最大深度]")
        print("示例: python dependency_extractor.py ostd::src::mm::frame::linked_list::LinkedList::push_front")
        sys.exit(1)
    
    function_path = sys.argv[1]
    max_depth = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    
    extractor = DependencyExtractor()
    dependencies = extractor.extract_dependencies(function_path, max_depth)
    extractor.print_dependencies(dependencies)


if __name__ == "__main__":
    main()
