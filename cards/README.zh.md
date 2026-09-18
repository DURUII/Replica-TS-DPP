# Cards — 定理卡、证明卡与依赖 DAG

[English](README.md) | 中文

每张卡片一个文件。一张卡片为 **CLOSED**，当且仅当 (a) 其 Lean 声明可构建且不含 `sorry`，
且 (b) `#print axioms` 返回 `{propext, Classical.choice, Quot.sound}` 的子集。
下文每张卡片都记录它*消耗*的卡片，并且——这正是 DAG 的意义所在——记录**它的哪些依赖仍然
敞开**，使读者一眼就能看出某个结论有多大一部分建立在未证明的地基之上。

`../DESIGN.md` §3 中的状态板由 `lake build` 输出重新生成；本目录是它的可读展开。

## DAG

```
                    R1 ──────────────────┐
                                         ├──► R12a ──── (δ ≤ C hypothesis) ──┐
                    R2 ──────────────────┘                                   │
                     │                                                       │
                     └──► R5 ──► R6 ─────────────────────────────┐          │
                                                                 │          │
                    R8 ──► R9 (Lemma 2) ─────────────────────────┤          │
                                    ▲                             │          │
                    R3 ──► R15 ────┘                             │          │
                                                                  ▼          ▼
                                         R10  (Eq 36, Eq 37)  ◄──────────────┘
                                                  │
                    R11 (Eq 38 assembly) ◄────────┘
                                                  │
     R7 (Thm 1) ──────────────────────────────────┤
                                                  ▼
     R14 (Eq 39) ─────────────────────────────► R16  ──►  R17 = ROOT (Theorem 2)
                                                  ▲            ▲
     R13 (Eq 40) ─────────────────────────────────┘            │
                                                                │
     R11 (Eq 38 assembly) ──────────────────────────────────────┘

  Open dependency (carried as a hypothesis, never as an axiom):
     L34 = Lemma 3 + Lemma 4  ([28])   ──► consumed by R11     ** partly — see below **
     L5  = Lemma 5            ([45])   ──► consumed by R13 and R16

  Out of scope (no Lean node at all — see R4.md):
     P1 = Eq (5)–(7)   ─┐
     R4 = Eq (10),(12),(13) ─┴─► the constrained policy; stands in for by the
                                 *hypotheses* of `theorem2_rate`, not by a node
```

`L34`——论文的 Lemma 3 + Lemma 4——是**部分**完成的。这两半必须分开报告，因为承载它的
三个声明并不都具有相同的分量：

* **Lemma 3 的组合学那一半是一条定理。** `sum_range_blocks` 把时域 `T = m·L` 切成 `m` 个
  长度为 `L` 的块，`regret_decomp_episodeOf` 提供了 Eq (27) 的望远镜求和，所以 `hdecomp` 是
  *推出来的*——**在 `theorem3_rate` 中**，它在 `BR := ∑ s ∈ range (m*L), r s` 处调用
  `theorem2_rate`，并在该实例化处闭合了前提。`Theorem2.lean` 中一般形式的 `theorem2_rate`
  仍按设计把 `hdecomp` 作为前提：它是在抽象 `BR : ℝ` 之上的陈述。`Decomp.lean` 说得很明确，
  这一切都不会消除 Lemma 3 的*另一半*——`∫` 在有限指标集上的线性性：*“消失的是「分解成立」
  这一假设，而不是「有东西可供分解」这一假设。”*
* **Lemma 4 已被证明，而且是在其最一般的形式下**——但它没有被接线接入，`hper` 仍被假设。
  `simulation_lemma` 在一个**任意**测度空间上做望远镜求和
  `∫ ω, ΔJ 0 ω ∂μ = ∑ t ∈ range L, ∫ ω, g t ω ∂μ`，其中 `bellman_step_le` 提供其 Bellman 递推
  `hrec`；二者都不含任何 bandit 内容。缺的是实例化：`Theorem2.lean` 导入的是
  `Mathlib, Decomp, Regret, Assembly, Tail, Rate`——**而不是 `Simulation`**——并且 `hper` 仍是
  `theorem2_rate` 和 `theorem3_rate` 二者的*假设*。`Simulation.lean` 自己的卡片把这一点说得很准确：
  它声称完成的是“*part of* `hper`”，而不是它的全部。缺失的一步是模型——轨迹律 `P_{θ*}` 与后验
  采样 `θ^l ∼ Q^l`，即 `DESIGN.md` **GAP-7**——而不是那条引理。

  （`R4` 是一个**不同的**缺席簇——Eq (10),(12),(13) 的受约束策略，列在上文“Out of scope”之下
  ——DAG 中没有任何东西消耗它。它不是这里的阻塞点；不要把两者混为一谈。）

引用节点出现在上面的 DAG 中，使读者能看到 `hper` 那一半现在仍然**敞开**在哪里。

`L5` 是 DAG 中唯一仍然敞开的**引用**。（`L34` 的 `hper` 那一半作为*假设*是敞开的，但它的数学
内容已被证明；两者是不同种类的敞开，并且分开计数。）它从来不是 `axiom`：每一条会用到它的 Lean
陈述都把它作为*显式假设*，因此读者能确切看到假设了什么、在哪里假设。当前状态见 `../DESIGN.md`
GAP-2——union-bound 路线被证明其上界为 `0.8839970429 = e/(e−1)·e^{−1/(e−1)}`，其 `−log` 为
`0.123302 < 0.125`，所以 artifact 采用 `c = 11/100` 而非论文的 `1/8`，差异在 `../FIDELITY.md`
§3.4 中量化。

**`L5` 正在闭合中**（卡片 `L5.md`）。它的子 DAG 如下，其中每一项或已证明、或在推进中：

```
  TSDPP.gammaMeasure_prod_ratio      (set-level Beta–Gamma ratio law)   CLOSED  BetaGamma.lean
        │
        ├──► gamma_ratio_isBetaMeasure  (map-level, via ext_of_Ici)   CLOSED  GammaRatioMap.lean
        │           │
  TSDPP.gammaMeasure_lintegral_exp      (Gamma Laplace transform)       CLOSED  GammaMGF.lean
        │           │
  TSDPP.gammaMeasure_prod_meas_le       (Markov on the product measure) CLOSED  TSDPP/
        │           │
  TSDPP.betaMeasure_Ici_le / _Iio_le    (the two one-sample tails)      CLOSED  TSDPP/
        │           │
  TSDPP.unionWitness                    (two-case numeric witness)      CLOSED  TSDPP/
        │           │
        ▼           ▼
  betaMeasure_abs_sub_concentration     (Eq (31) at c₀ = 11/100)        OPEN
```

闭合 `L5` 带来的两个超出它自身的后果：

1. **`TSDPP/` 之外的模块不在任何闭包中。** `TSDPP/BetaGammaChernoff.lean` 与
   `TSDPP/UnionBound.lean` 位于根模块的导入闭包之内，所以 `lake build TSDPP` 会编译它们，
   `lean4/scripts/check_axioms.sh` 会审计它们；已用
   `lake build TSDPP.BetaGammaChernoff TSDPP.UnionBound` 验证（通过，8933 个 job）。
   同一文件放在 `Scratch/` 下则不行：`lakefile.toml` 恰好声明了一个 `lean_lib`
   （`name = "TSDPP"`），而 `Scratch/` 没有 olean，所以 `import Scratch.BetaGammaChernoff`
   根本无法解析，装配文件将无从触及其所消耗的引理。`TSDPP/` 内任何地方都没有声明名冲突；
   `Scratch/` 下的冗余副本已删除，而不是任其漂移。
2. **常数会传播。** 论文的 `8` 是*耦合*的——它同时出现在 Lemma 5 的指数与半径
   `r = √(8 log T/α)` 中。我们的 `c₀` 迫使 `Rate.lean` 中 `K ≥ 1/c₀ = 100/11`，并在
   `Tail.lean` 中以 `cη`（参数 `c`，论文为 `1/8`，artifact 为 `11/100`）替代 `η/8`。
   `R13` 和 `R16` 按论文的陈述为真，但它们不是链条所消耗的陈述；两者现均**陈述**于
   `K₀ = 100/11`（`Tail.lean` 的指数是参数 `c`，`Rate.lean` 的被开方数是 `(100/11)`，
   `two_mul_sqrt_eight_le` 更名为 `two_mul_sqrt_ratio_le`，最终常数为 `8`，在
   `2√(100/11) + 1 = 7.030227` 处接近紧）。已验证：`lake build TSDPP` 通过；
   `lean4/scripts/check_axioms.sh` 审计 `Audit.lean` 中列出的声明，每条或不依赖任何东西、或依赖于
   `{propext, Classical.choice, Quot.sound}` 的子集。速率 `O(√(L³T log T))` 不变——
   几何级数对每个 `c > 0` 都收敛。

`R4` 不是*敞开*节点，而是一个**缺席**节点——论文的问题陈述从未被形式化，所以 DAG 中没有任何
东西消耗它。`R4.md` 记录它，以替代否则将会缺失的那个文件。

| 卡片 | 文件 | 状态 |
|------|------|--------|
| R1  | `R1.md`  | CLOSED |
| R2  | `R2.md`  | CLOSED |
| R3  | `R3.md`  | CLOSED |
| R4  | `R4.md`  | **NOT FORMALIZED** — Eq (10),(12),(13)；受约束策略。超出范围，不是公理 |
| R5  | `R5.md`  | CLOSED |
| R6  | `R6.md`  | CLOSED |
| R7  | `R7.md`  | CLOSED |
| R8  | `R8.md`  | CLOSED |
| R9  | `R9.md`  | CLOSED |
| R10 | `R10.md` | CLOSED |
| R11 | `R11.md` | CLOSED |
| R12a| `R12a.md`| CLOSED |
| L34 | (citation, [28]) | **PARTLY** — L3 的组合学那一半已推出（`regret_decomp_episodeOf`，被 `theorem3_rate` 使用）；L4 *已证明*（`simulation_lemma`、`bellman_step_le`）但**未被实例化**，所以 `hper` 仍是一个假设。阻塞于 GAP-7，而非 R4 |
| L5  | (citation, [45]) | **NOT CLOSED — 注册形式为 FALSE**（陷阱 P-64，见 `L5.md`）。artifact 陈述的是 `r ≥ 1`；论文陈述的是 `0 ≤ r ≤ 1`。在 `r ≥ 1` 上，界在 `(α,β,r) = (2,200,10)` 处失效：精确值 `8.6066401e−09` 对比注册界 `5.5789e−10`，超出 **15.43×**。所有*已交付*的东西都是真实的，并予保留：条件式 `hnum ⟹ bound`、两条精确的单样本 Chernoff 尾界、union-bound 核心，以及四个 `'`-形式。比值律 **CLOSED**（`BetaGamma.lean`）；映射层面的焊接 **CLOSED**（`GammaRatioMap.lean`）；常数传播至 R13/R16，见 `Tail.lean` 与 `Rate.lean`。旧的上限断言（`0.123302 < 1/8` ⟹ `c₀ = 11/100`）已**被撤回**（P-62 第 1–3 层），`c₀ = 11/100` 现为 **[UNDERIVED]**；至于为什么改在论文的取值范围内重述也修不好论文的*应用*，见 `DESIGN.md` J-11。**由 P-67 扩展**：在 Eq (33) 自身的参数曲线 `r = max{1,√(8 log T/α)}` 上，**论文的** `1/8` 在 6 个抽样元组中有 5 个失效（含 `α=1, T=10⁶`），所以论文的*用法*在论文自己的设定上就是假的，而不只是 artifact 的形式化。**该反证本身现在也是一项交付物**（`CLAUDE.md` 第 1 条允许 "完整证明**或反证**"）：卡片 **`L5-REFUTATION.md`** 载有该证书——见证 `(α,β,r) = (1,100,14)`、初等包含关系 `{X ≥ 15/101} × {Y ≤ 1/101} ⊆ {\|X−Y\| ≥ 14/101}`、可证下界 `LB = (86/101)^100·(1−(100/101)^100)`，超出注册界 **75.79×**（并超出真实概率 **353.48×**）。机器校验形式：**`lean4/TSDPP/Lemma5Refutation.lean` — CLOSED，无条件，已审计。** 两条主定理（`11/100` 处的 `lemma5_as_registered_is_false`、论文自己的 `1/8` 处的 `paper_lemma5_range_ge_one_is_false`）都**不带任何假设**；它们的解析输入是 `lean4/TSDPP/BetaOneCDF.lean`（闭式的 `Beta(1,B)` 尾）。已构建进根闭包，并由 `lean4/scripts/check_axioms.sh` 审计。**范围——引用本条之前请先读 `L5-REFUTATION.md` §0：** 被反驳的是 **`r ≥ 1`** 的陈述；论文自己的 Lemma 5（第 9 页 Eq (31) 将其陈述于 **`0 ≤ r ≤ 1`**）**没有**被反驳（见证位于 `r = 14`，在该范围之外），论文的定理也没有——一个走不通的证明步骤并不会使定理为假 |
| R13 | `R13.md` | CLOSED（陈述于尾部指数参数 `c > 0`） |
| R14 | `R14.md` | CLOSED |
| R15 | `R15.md` | CLOSED |
| R16 | `R16.md` | CLOSED（陈述于 `K₀ = 100/11`；最终常数 `8`） |
| R17 | `R17.md` | CLOSED（**ROOT** — Theorem 2 已装配） |
