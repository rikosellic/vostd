#!/usr/bin/env python3
"""
依赖关系提取器（简化版）
从Verus验证日志中提取给定函数的所有依赖项
单一crate版本
"""

import re
import sys
from pathlib import Path
from typing import Set, List


class DependencyExtractor:
    def __init__(self, verus_log_dir: str = ".verus-log"):
        self.verus_log_dir = Path(verus_log_dir)
        self.vir_files: List[Path] = []
        
        # 扫描所有验证文件
        self._scan_vir_files()
    
    def _scan_vir_files(self):
        """扫描.verus-log目录下所有的poly.vir文件"""
        if not self.verus_log_dir.exists():
            print(f"错误：目录 {self.verus_log_dir} 不存在")
            return
        
        self.vir_files = list(self.verus_log_dir.glob("**/*-poly.vir"))
        print(f"发现 {len(self.vir_files)} 个验证文件", file=sys.stderr)
    
    def _normalize_path(self, path: str) -> str:
        """
        将验证文件中的路径标准化为模块路径
        
        参数:
            path: 验证文件中的路径（如 "lib!mm.frame.linked_list.LinkedList."）
        
        返回:
            标准化的路径（如 "mm::frame::linked_list::LinkedList"），或None如果应该过滤
        """
        # 移除尾部的点
        path = path.rstrip('.')
        
        # 过滤掉匿名impl块和其他自动生成的项目
        if 'impl&%' in path or 'anonymous_closure' in path or 'verus_builtin' in path:
            return None
        
        # 移除lib!前缀（表示当前crate）
        if path.startswith("lib!"):
            path = path[4:]
        # 过滤标准库
        elif path.startswith(('vstd!', 'core!', 'alloc!', 'std!')):
            return None
        
        # 将点号替换为::
        return path.replace('.', '::')
    
    def _extract_function_module_path(self, function_path: str) -> tuple:
        """
        从函数路径中提取模块路径和函数名
        
        参数:
            function_path: 如 "mm::frame::linked_list::LinkedList::push_front"
        
        返回:
            (module_path, function_name)
        """
        parts = function_path.split("::")
        
        if len(parts) < 2:
            raise ValueError(f"无效的函数路径: {function_path}")
        
        # 最后一个或两个部分是函数名
        if len(parts) >= 3:
            module_parts = parts[:-2]
            type_and_func = parts[-2:]
            module_path = '.'.join(module_parts)
            function_name = '::'.join(type_and_func)
        else:
            module_path = ""
            function_name = parts[-1]
        
        return module_path, function_name
    
    def _find_module_files(self, module_path: str) -> List[Path]:
        """
        查找包含指定模块的验证文件
        
        参数:
            module_path: 模块路径，用点分隔（如 "mm.frame.linked_list"）
        
        返回:
            匹配的文件路径列表
        """
        if not module_path:
            # 如果没有模块路径，返回所有文件
            return self.vir_files
        
        # 将模块路径转换为文件名模式
        file_pattern = module_path.replace('.', '__')
        
        matching_files = []
        for vir_file in self.vir_files:
            if file_pattern in vir_file.stem:
                matching_files.append(vir_file)
        
        return matching_files
    
    def _parse_vir_file(self, vir_file: Path) -> Set[str]:
        """
        解析VIR文件，提取所有依赖的类型和函数
        
        参数:
            vir_file: VIR文件路径
        
        返回:
            依赖项集合
        """
        dependencies = set()
        
        try:
            with open(vir_file, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
            
            # 提取所有路径引用
            # 匹配格式: (Dt Path "lib!mm.frame.linked_list.LinkedList.")
            path_pattern = r'\(Dt Path "([^"]+)"\)'
            for match in re.finditer(path_pattern, content):
                path = match.group(1)
                normalized = self._normalize_path(path)
                if normalized:
                    dependencies.add(normalized)
            
            # 提取trait引用
            # 匹配格式: (TraitId Path "lib!cast_ptr.Repr.")
            trait_pattern = r'\(TraitId Path "([^"]+)"\)'
            for match in re.finditer(trait_pattern, content):
                path = match.group(1)
                normalized = self._normalize_path(path)
                if normalized:
                    dependencies.add(normalized)
            
            # 提取函数调用
            # 匹配格式: (FunId Path "lib!mm.frame.linked_list.LinkedList.push_front.")
            fn_pattern = r'\(FunId Path "([^"]+)"\)'
            for match in re.finditer(fn_pattern, content):
                path = match.group(1)
                normalized = self._normalize_path(path)
                if normalized:
                    dependencies.add(normalized)
                
        except Exception as e:
            print(f"警告：解析文件 {vir_file} 时出错: {e}", file=sys.stderr)
        
        return dependencies
    
    def extract_dependencies(self, function_path: str, max_depth: int = 5) -> Set[str]:
        """
        提取给定函数的所有依赖项
        
        参数:
            function_path: 函数的完整路径（如 "mm::frame::linked_list::LinkedList::push_front"）
            max_depth: 最大递归深度
        
        返回:
            所有依赖项的集合
        """
        # 解析函数路径
        module_path, function_name = self._extract_function_module_path(function_path)
        
        print(f"\n分析函数: {function_path}", file=sys.stderr)
        print(f"  模块: {module_path}", file=sys.stderr)
        print(f"  函数: {function_name}", file=sys.stderr)
        
        # 查找相关的验证文件
        module_files = self._find_module_files(module_path)
        
        if not module_files:
            print(f"警告：未找到模块 {module_path} 的验证文件", file=sys.stderr)
            return set()
        
        print(f"\n找到 {len(module_files)} 个相关文件", file=sys.stderr)
        
        # 用于追踪已处理的依赖，避免重复处理
        processed = set()
        to_process = set()
        all_dependencies = set()
        
        # 首先处理主模块文件
        for vir_file in module_files:
            deps = self._parse_vir_file(vir_file)
            all_dependencies.update(deps)
            to_process.update(deps)
        
        # 递归处理依赖
        depth = 0
        while to_process and depth < max_depth:
            depth += 1
            print(f"深度 {depth}: 处理 {len(to_process)} 个依赖项...", file=sys.stderr)
            
            current_batch = to_process - processed
            to_process = set()
            
            for dep in current_batch:
                processed.add(dep)
                
                # 从路径中提取模块部分
                dep_parts = dep.split("::")
                if len(dep_parts) >= 2:
                    # 假设最后一个是类型/函数名
                    dep_module = '.'.join(dep_parts[:-1])
                    dep_files = self._find_module_files(dep_module)
                    
                    for vir_file in dep_files:
                        new_deps = self._parse_vir_file(vir_file)
                        new_deps = new_deps - processed
                        all_dependencies.update(new_deps)
                        to_process.update(new_deps)
        
        return all_dependencies
    
    def print_dependencies(self, dependencies: Set[str]):
        """打印依赖项，排序输出"""
        print("\n" + "="*80)
        print("依赖项列表")
        print("="*80 + "\n")
        
        for dep in sorted(dependencies):
            print(f"  {dep}")
        
        print(f"\n总计: {len(dependencies)} 个依赖项")
        print("="*80)


def main():
    if len(sys.argv) < 2:
        print("用法: python dependency_extractor.py <函数路径> [最大深度]")
        print("示例: python dependency_extractor.py mm::frame::linked_list::LinkedList::push_front")
        sys.exit(1)
    
    function_path = sys.argv[1]
    max_depth = int(sys.argv[2]) if len(sys.argv) > 2 else 5
    
    extractor = DependencyExtractor()
    dependencies = extractor.extract_dependencies(function_path, max_depth)
    extractor.print_dependencies(dependencies)


if __name__ == "__main__":
    main()
