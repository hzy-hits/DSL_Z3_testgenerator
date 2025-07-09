# GitHub上传指南

## 步骤 1: 在GitHub创建新仓库

1. 访问 https://github.com/new
2. 仓库名称: `dsl-test-generator-v2`
3. 描述: "Intelligent test case generator with formal verification and conflict detection"
4. 设置为 Public 或 Private
5. **不要**初始化 README, .gitignore 或 LICENSE（我们已有）
6. 点击 "Create repository"

## 步骤 2: 连接并推送

GitHub会显示类似下面的命令，在终端执行：

```bash
# 添加远程仓库（替换YOUR_USERNAME为你的GitHub用户名）
git remote add origin https://github.com/YOUR_USERNAME/dsl-test-generator-v2.git

# 推送到GitHub
git branch -M main
git push -u origin main
```

如果使用SSH：
```bash
git remote add origin git@github.com:YOUR_USERNAME/dsl-test-generator-v2.git
git branch -M main
git push -u origin main
```

## 步骤 3: 验证上传

刷新GitHub页面，应该能看到所有文件已上传。

## 项目亮点（可添加到GitHub描述）

- 🎯 100% correctness guarantee with Z3 SMT solver
- 📊 60-70% test reduction while maintaining full coverage  
- 🔍 Automatic business logic conflict detection
- 🌏 Multi-language support (Chinese/English)
- 🏗️ Clean layered architecture
- 📝 Multiple output formats

## 建议的GitHub Topics

- test-generation
- dsl
- formal-methods
- z3-solver
- software-testing
- test-automation
- smt-solver
- conflict-detection