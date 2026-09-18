# Lemma5PaperRange — Lean 陷阱与路线陷阱（本地编号，与 DESIGN.md 的 P-xx 不共用）

工作文件：`lean4/TSDPP/Lemma5PaperRange.lean`（`lake env lean` exit 0，无 `sorry`）。
每条格式：`* **P-xx (一句话断言)** 现象/原文报错；Rule: 以后怎么做`

## A. Lean 陷阱（本文件实打实撞到的）

* **P-01 (`λ` 不能作绑定变量名)** `def f (α β : ℝ) : Prop := ∀ λ : ℝ, 0 ≤ λ → ...` 报
  `error: unexpected token 'λ'; expected '(', '[', '_', '{', '⦃' or identifier`（`λ` 被词法分析成
  lambda 记号，不是标识符）；Rule: 绑定变量一律用 `t`/`lam`；`λ` 只在项位置作 lambda 记号用。

* **P-02 (`Set.mem_setOf_eq` 已弃用)** `simp only [Set.mem_setOf_eq]` 触发
  `warning: 'Set.mem_setOf_eq' has been deprecated: Use 'Set.mem_ofPred_eq' instead`；Rule: 一律写
  `Set.mem_ofPred_eq`（与 `TSDPP/BetaConcentration.lean` 现有写法一致）。

* **P-03 (`ofReal_measureReal` 的命名空间)** `Measure.ofReal_measureReal` 报
  `error(lean.unknownIdentifier): Unknown constant 'MeasureTheory.Measure.ofReal_measureReal'`；真正的名字在
  `MeasureTheory` 根命名空间（`Mathlib/MeasureTheory/Measure/Real.lean:65`：
  `theorem ofReal_measureReal (h : μ s ≠ ∞ := by finiteness) : ENNReal.ofReal (μ.real s) = μ s`）；Rule:
  `open MeasureTheory` 后直接写 `ofReal_measureReal`，不要加 `Measure.` 前缀。

* **P-04 (`Measure.real_mono` 不存在)** 报 `Unknown constant 'MeasureTheory.Measure.real_mono'`；实际名是根命名空间的
  `measureReal_mono (h : s₁ ⊆ s₂) (h₂ : μ s₂ ≠ ∞ := by finiteness) : μ.real s₁ ≤ μ.real s₂`，第二个参数是
  `autoParam`（由 `finiteness` 自动填，需要 `IsFiniteMeasure` 实例）；Rule: 概率测度上先 `haveI : IsProbabilityMeasure μ`
  再调 `measureReal_mono`，别手写有限性。

* **P-05 (`map_apply` 的两套签名)** `Measure.map_apply` 要求 `Measurable f`（不是 `AEMeasurable`）：`Measure.map_apply (hf : Measurable f) {s : Set β} (hs : MeasurableSet s) : (Measure.map f μ) s = μ (f ⁻¹' s)`；
  可测性弱化版是 `map_apply_of_aemeasurable`；Rule: 集合的水平集走 `isClosed_le continuous_const (continuous_fst.sub continuous_snd) |>.measurableSet` 拿 `MeasurableSet`，再配 `measurable_swap`。

* **P-06 (`prod_swap` 需要 `SFinite`)**
  `Measure.prod_swap : Measure.map Prod.swap (μ.prod ν) = ν.prod μ`（`Prod.lean:689`）带 `[SFinite μ] [SFinite ν]`；
  在 `μ = betaMeasure α β` 上由 `IsProbabilityMeasure → IsFiniteMeasure → SFinite` 自动满足，但**必须**先
  `haveI : IsProbabilityMeasure μ`；Rule: 用 `prod_swap` 前先立概率实例，否则报 typeclass 合成失败。

* **P-07 (`Prod.swap p` 的 `.1/.2` 不会自动化简)** `simp only [Set.mem_preimage, Set.mem_ofPred_eq, Prod.swap_prod_mk]`
  后目标里仍是 `p.swap.1 - p.swap.2`（`Prod.swap_prod_mk` 只对**构造子** `(a,b).swap` 生效，对变量 `p` 无效），
  `linarith` 随即失败（把 `p.swap.1` 当作与 `p.2` 无关的原子）；Rule: 用 `Prod.fst_swap`/`Prod.snd_swap` 显式化简，
  或 `cases p` 后再 simp。

* **P-08 (Markov 引理要求 `Integrable`，逼出"假设里捆绑可积性"的设计)**
  `mul_meas_ge_le_integral_of_nonneg (hf_nonneg : 0 ≤ᵐ[μ] f) (hf_int : Integrable f μ) (ε : ℝ) : ε * μ.real {x | ε ≤ f x} ≤ ∫ x, f x ∂μ`
  （`MeasureTheory/Integral/Bochner/Basic.lean:1162`）。`∫⁻ (ofReal f) ≤ ofReal (∫ f)` 是**错误方向**（Bochner 积分在不可积时返回 0），
  而 `lintegral` 路线的方向恰好相反、推不出结论；Rule: 走 Bochner 时把 `Integrable` 一起写进残差假设
  （`BetaProdMGFBound` 里 `Integrable ... ∧ ... ≤ ...`），不要试图用 `∫⁻` 绕开——绕不过去。

* **P-09 (`2 * ofReal x = ofReal (2 * x)` 不能靠 `ofReal_natCast`)** `rw [← ENNReal.ofReal_natCast 2, ...]` 报
  `Tactic rewrite failed: Did not find an occurrence of the pattern ↑2`；Rule: 直接
  `rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]` 再 `norm_num`。

* **P-10 (`simp only [Set.mem_ofPred_eq]` 不拆 union)** 只写 `Set.mem_ofPred_eq` 时目标里的
  `p ∈ S₁ ∪ S₂` 不会变成析取（`Set.mem_union` 不在给定集合里），`Or.inl` 会莫名其妙地"成功"、而第二个分支
  `linarith` 报 `failed`；Rule: 需要拆并集时把 `Set.mem_union` 一起写进 `simp only` 列表。

* **P-11 (`linarith` 把 exp 的不同书写法当不同原子)** `h : 1/2 ≤ Real.exp (-(1/8 * α * r^2))` 与目标
  `1 ≤ 2 * Real.exp (-(1/8) * α * r^2)` 中两个 `Real.exp` 参数在语法上不同（`-(1/8 * …)` vs `-(1/8) * …`），
  `linarith` 报 `failed to find a contradiction` 且上下文里显示 `a✝ : Real.exp (...) < 1/2`；Rule: 先用
  `have hkey : -(1/8:ℝ) * α * r^2 = -(α * r^2 / 8) := by ring` 把**目标**重写成与假设同形，再 `linarith`。

* **P-12 (`one_div` 之后再 `← Real.exp_neg` 不成立)** `rw [one_div, ← Real.exp_neg]` 报
  `Did not find an occurrence of the pattern (Real.exp ?x)⁻¹`；Rule: 不要走除法，直接把目标化成
  `exp` 的单调性（`Real.exp_le_exp.mpr` + `Real.exp_log`）再 `linarith`。

* **P-13 (`lake env lean` 不构建被 import 模块的 olean)** 直接 `lake env lean Scratch/X.lean` 会在 import 处失败；
  Rule: 先 `lake build TSDPP.BetaConcentration`，再 `lake env lean Scratch/X.lean`（本次首调即撞到，构建 8936 jobs 后正常）。

## B. 路线级陷阱（不是 Lean 报错，但同样"以后别这么走"）

* **P-14 (union bound + Chernoff 的损失是多项式因子，不是 1.4%)** 在 `ρ = β/α ≫ 1` 的远尾，
  `chernoffA (β/α) δ ^ α` 与真尾概率之比是 **20–80 倍**（α=1000, ρ=100：δ=0.3 时 24×，δ=1 时 80×），
  即损失 3–4.4 nats；而 union 路线在那个区域只比目标松 ~0.36 nats。**结论：union+Chernoff 在 ρ≫1 处
  定性失效（随 α 增长），不是"差 1.4%"的小缺口**——与 DESIGN.md P-64/GAP-2b 的 0.884 天花板是同一现象的两种测法。
  同一 (α,β,r) 上用**精确尾**做 union 的最优值只有目标的 0.035 倍，说明瓶颈是尾估计质量，不是 union 结构本身。
  但精确尾 = 不完全 Beta / ₁F₁，Mathlib 没有；Rule: 不要再用 union+Chernoff 尝试纸面常数 1/8。

* **P-15 (小 ρ 侧的"失败"是网格假象)** `ρ = β/α ≪ 1` 时最优点在边界 `δ₁ → ρ`（等价 `t₁ → 1`，上尾=0），
  只有取到 `ε = ρ − δ₁` 极小时才能把 `chernoffA` 压到目标以下；粗网格会报出天文数字的"比值"。
  Rule: 报数值失败前先确认最优点不在参数边界上（DESIGN.md P-20 的同类错误）。

* **P-16 (MGF 路线 = 单节点 (C))**(C) `M(λ)M(−λ) ≤ e^{2αλ²/(α+β)²}`（0 ≤ λ ≤ (α+β)/4）等价于
  (T'') `Var_u(X) ≤ 2 Var(X)`（|u| ≤ (α+β)/4）；(T'') 的全局上确界 = **16/9 = 1.7778 < 2**，仅在
  α→0、β→∞、u=(α+β)/4 处逼近（尖峰极限），因此**任何证明必须在尖峰极限精确到因子 ~1.12 以内**；
  Rule: 不要指望"用一个粗放不等式 + 一点余量"闭合 (T'')。

* **P-17 (ᵢFᵢ 不在 Mathlib)** (T'')/(C) 目前唯一的已知充分链（子代理给出）归结为
  `(λ/γ)·₁F₁(α+1;γ+1;λ) ≤ (1/3)·₁F₁(α;γ;λ)`（0 ≤ λ ≤ γ/4）——Mathlib 里没有 ₁F₁，Beta 的 MGF 也没有；
  Rule: 走 (C) 路线前先想清楚用什么初等对象"代替 ₁F₁"（例如 Riccati ODE `(u·n)' = γ·Var_u` / `u·n = γm−α`
  这类只用密度矩的恒等式），否则形式化会卡在"没有这个函数"而不是"没有这个证明"。

* **P-18 (α→0 的极限与 t→0 的展开不可交换；换错了会伪造出反例)**  残差假设 `BetaProdMGFBound`
  就是 (C)，对它做数值对抗（`₁F₁(α;c;t)·₁F₁(α;c;−t)` 对 `e^{2αt²/c²}`，`c = α+β`，`0 ≤ t ≤ c/4`）：
  **1632 格点、0 违反**，非平凡最差 `LHS/RHS = 0.99999999999375`，在
  `(α, β, t/t_max) = (1e-4, 1e24, 1e-3)`。三个操作要点：
  (i) `t = 0` 必须从网格里排除——那里 `LHS = RHS = 1` **恒等**，留在里面会盖过非平凡最差、
  把扫描的"最差"报成那个平凡等号；
  (ii) `mpmath.hyp1f1` 在 α 大时根本不收敛（`hypsum` 报"需要 7204 bits"，α=10000 的全部格点直接
  `ValueError`），用 Kummer `₁F₁(a;c;z) = eᶻ·₁F₁(c−a;c;−z)` 换成 `min(α,β)` 作第一参数即可，
  而把该恒等式代进乘积**顺带证明了 `LHS` 在 `α↔β` 下不变**（`X−Y` 与 `Y−X` 同分布，
  `t_max = c/4` 也不变），于是那些"失败"格点由对称性免费得到；
  (iii) **陷阱本身**：`α→0` 的极限 `LHS → (1+cosh t)/2` 只在 **`t` 固定**时成立。本网格最紧的角落
  恰恰是 `α→0` 与 `t→0` **同时**发生，两个极限不可交换。若用那个闭式的浅展开
  `1 + t²/4` 去比 `RHS ≈ 1 + 2αt²/c²`，则 `c² > 8α` 时得 `LHS > RHS`——而此处
  `c² = 1e48 ≫ 8α = 8e-4`，**据此会报出一个不存在的反例**。保留一阶项后
  `RHS − LHS ≈ αt²/c² = 6.25e-12`，与数值给出的 `1 − LHS/RHS = 6.25e-12` **逐位吻合**。
  Rule: 双重退化极限下先写**两项**展开再比较；"先取 α→0"的闭式把 `t` 当常数，而最紧的角落
  正是 `t` 也一起退化。**等号在退化角落被任意逼近但从未越过**——这既是 (C) 为真的证据，
  也说明任何证明都不能在尖峰附近留下常数松弛。

* **P-19 (上尾公式写成了下尾，且化简后**看不出来**)** 验证 `h(x) = P(X>x) − P(Y>x)` 时，
  `P(Y>x)` 写成 `e^{−cs}(cs)^α·₁F₁(1;α+1;cs)/Γ(α+1)`。α=1 时 `₁F₁(1;2;w) = (e^w−1)/w`，
  该式**恰好化简为 `1 − e^{−cs}`，即 `P(Y ≤ x)`**。代入 `(α,β) = (1,1)` 得到的是
  `e^{−2x} = x` 的根 `0.4275`，而非真解 `(1−x) = e^{−2x}` 的根 `0.7968`。
  整批 `changes=3 pattern=+--++-` 的输出因此全部作废。
  Rule: 整数 α 时直接用**全正项**闭式 `P(Γ(α,rate c) > s) = e^{−cs}·Σ_{k<α}(cs)^k/k!`，
  不要走 `1 − (下尾)`；并且**判定前必须先用闭式锚点验函数本身**——`(1,1)`、`(1,100)`、`(1,1000)`
  三组都有初等闭式，`SX − SY` 与它们应在工作精度下**逐位相等**（`==`，不是"接近"）。

* **P-20 (网格未排序，回跳处伪造符号变化)** 扫描网格由两段拼接
  `[1e-7…1e-1] ++ [0.002,0.004,…]`，`0.1` 之后接 `0.002` **往回跳**。于是每跨越一次回跳就把
  已确定的符号再记一次变化：`(1,100)`、`(5,500)`、`(4,400)`、`(1,50)` 全部报出 3 次变化。
  用闭式 `h = (1−x)^100 − e^{−101x}` 展开定出真交叉在 `x ≈ 1/50 = 0.02`，恰在回跳点之前——
  **一个假交叉都没少**。Rule: 符号变化计数前 `sorted(set(grid))`，并断言网格严格递增
  （`all(XS[i] < XS[i+1])`）；拼接分段网格时显式检查段间连续性。

* **P-21 (网格有洞，交叉点位置被推迟；以及用未验证的"手算 oracle"当基准)**
  修好排序后对数段止于 `0.1`、线性段起于 `1.0`，`(0.1, 1.0)` 是空的，凡交叉落于该区间的
  案例（`(1,1)` 真值 `0.7968`）一律被报成 `1.0`。**次数**仍可信（跳跃只延迟不伪造），
  **位置**不可信。同一轮里我的自检"want"公式 `1 − 2s + s²` 本身是错的
  （`(2,3)` 处真值手算 `1 − 12∫₀^{0.1}(x−2x²+x³)dx = 0.94770`，正是代码返回的值），
  于是脚本报出的 `diff=0.138` 是**基准的错**，不是被测对象的错。
  Rule: (i) 分段网格覆盖必须无缝，交叉点位置与次数是两项独立断言，各自都要锚点；
  (ii) 自检公式必须能被**独立**手段（手算积分 / 另一条闭式）复核，否则"验证"只是把
  一个错误换到基准那一侧。

* **P-22 (验证器的结论只在验证器自身过锚之后才成立——本轮总账)** 本轮对同一命题
  「`h` 在 `(0,∞)` 上恰有一次 `+→−` 符号变化」先后给出四份互相矛盾的数值结论，
  其中**三份的偏差全部来自验证器而非被验证对象**（P-19 错尾、P-20 乱序、P-21 洞 + 错基准）。
  定稿脚本 `hsign6.py`：三组闭式锚点 `==` 逐位通过 → 无缝严格递增网格 1461 点、
  `|h| > 1e-45` 量级过滤 → **20/20 案例恰好一次 `+→−`**，交叉位置与闭式解一致
  （`(1,1)` 在 25 位上逐位相同：`0.7968121300200200461615209`）。
  Rule: 数值承重引理的顺序永远是**锚点 → 网格 → 量级过滤 → 判定**；锚点不过，
  脚本的**任何**输出（包括"通过"）都不算证据。数值通过仍只是数值通过，不等于证明。
