# Lean 无除法算术库

[English](README.md) | 简体中文

我们在本库中用 Lean 形式化任意含幺交换环（包括零环）上的无除法算术，提供受限算术电路及其正确性、运算门数和线性结构的证明，涵盖多项式乘法、幂级数逆、首一约化和线性程序转置。

## 主要结果

以下渐近界以系数向量长度 `n` 为参数；主要多项式算术定理也处理零长度和零环。

- **完整多项式乘法：** `fastFullMultiplier` 计算两个长度为 `n` 的系数向量的完整乘积。实际 Cantor–Kaltofen 电路的总算术门数为 `O(n log n log log n)`，其中乘法门数为 `O(n log n)`；整数常数的总位数为 `O(n log n)`。这些界包含变换准备、补零、归一化和 Bézout 合并。见 `Polynomial.FastMultiplication`、`Polynomial.CantorMultiplication` 和 `Polynomial.CantorFullBounds`。
- **双线性与固定因子程序：** 完整乘积有具备共享预处理的双线性替代电路，总门数为 `O(n log n log log n)`，乘法秩为 `O(n log n)`。固定因子的前向及转置线性程序也包含参数准备，其总门数为 `O(n log n log log n)`。见 `Polynomial.CantorBilinear` 和 `Polynomial.CantorPreparedLinear`。
- **幂级数逆与首一约化：** 常数项为一的幂级数逆和完整首一余数具有 `O(n log n log log n)` 算术门数界。首一约化的固定模数前向及转置线性程序包含反射逆的准备。见 `Polynomial.SeriesInverse`、`Polynomial.CantorNewtonCost`、`Polynomial.MonicReduction` 和 `Polynomial.MonicPreparedLinear`。
- **转置与多元编码：** 矩形线性程序转置支持共享中间值、重复输出和零输出；截断商环上的系数反转转置在正精度下也已证明。混合进制 Kronecker 乘积接口保留每维的完整输出范围。见 `LinearStraightLine.Transpose`、`LinearStraightLine.QuotientTranspose` 和 `Kronecker.FullProduct`。

门数按电路语法中的环加、取负和乘法计算，整数常数位数另计。部分定义是 `noncomputable` 的数学构造；门数界不是电路生成或 Lean 求值的运行时间界。更详细的证明范围及其边界见 [STATUS.md](docs/STATUS.md)，技术规格见 [REQUIREMENTS.md](docs/REQUIREMENTS.md)。

## 构建与使用

使用 `lean-toolchain` 固定的 Lean **4.32.0** 和 mathlib `81a5d257c8e410db227a6665ed08f64fea08e997`：

```bash
lake exe cache get
python3 scripts/check.py
```

检查脚本构建所有源模块、审计项目声明的公理并编译使用示例；公理仅允许 `propext`、`Classical.choice` 和 `Quot.sound`。下游项目可使用 Lake 引入本库，并导入 `DivisionFree` 或所需模块。完整乘法正确性定理的用法见下方示例及 [FullMultiplication.lean](examples/FullMultiplication.lean)。

## 来源

我们从 `matmul` 项目改编了 `Circuit.lean` 和 `Recurrence.lean`，并从我们的模复合形式化中提取了 `Lifting.lean`。源文件哈希、许可证和修改说明见 [PROVENANCE.json](docs/PROVENANCE.json)。本库采用 Apache-2.0 许可证，相关声明见 [NOTICE](NOTICE)。

## 示例

```lean
import DivisionFree.Polynomial.FastMultiplication

open DivisionFree.PolynomialArithmetic

example {R : Type} [CommRing R] (n : ℕ) (x : Bool × Fin n → R) :
    vectorPolynomial (2 * n) ((fastFullMultiplier.{0} n).circuit.eval x) =
      vectorPolynomial n (fun i => x (false, i)) *
        vectorPolynomial n (fun i => x (true, i)) := by
  exact fastFullMultiplier_correct n x
```

`false` 和 `true` 分别选择两个输入向量；输出有 `2 * n` 个系数，
`n > 0` 时末项为零。
