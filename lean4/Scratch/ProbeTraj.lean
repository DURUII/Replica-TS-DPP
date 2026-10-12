/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
TRAPS —— GAP-7 探针。

只回答一个问题:把轨迹律地基按 `rl-theory-in-lean/RLTheory/Probability/MarkovChain/Trajectory.lean`
的形状搭起来,在我们钉住的 mathlib(`f61f3ed7633ff99ecaae4a086395b501652a76ee`)上能不能**实例化通过**。

三问:
  A. 轨迹律 `P := traj κ 0 ∘ₘ (init.map constPrefix)` 能不能造在**任意** `[MeasurableSpace S]`
     (不带拓扑)上,并自动是 `IsProbabilityMeasure`?
  B. 自然滤子能不能用现成的 `Filtration.natural`?它要什么前提?
  C. 若 B 的拓扑前提不满足,能不能手写一个任意 `[MeasurableSpace S]` 下都能用的滤子?

不做证明性陈述(不碰"轨迹律满足什么性质"),不改 `TSDPP/` 下任何文件。`#check` 是**存在性证据**。
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TSDPP.ProbeTraj

/-! ## 0. 存在性:这版 mathlib 里到底有什么 -/

section Exists

#check @ProbabilityTheory.Kernel.traj
#check @ProbabilityTheory.Kernel.map_traj_succ_self
#check @ProbabilityTheory.Kernel.isProbabilityMeasure_trajFun
#check @ProbabilityTheory.Kernel.traj_comp_partialTraj
#check @ProbabilityTheory.Kernel.traj_eq_prod
#check @ProbabilityTheory.Kernel.traj_map_frestrictLe
#check @Filtration.natural
#check @Filtration.natural_eq_comap

end Exists

/-! ## A. 轨迹律 —— 任意 `[MeasurableSpace S]`,不带拓扑 -/

section Law

variable {S : Type*} [MeasurableSpace S]

def constPrefix (S : Type*) [MeasurableSpace S] : S → ((i : ↥(Finset.Iic 0)) → S) :=
  fun s _ => s

lemma measurable_constPrefix (S : Type*) [MeasurableSpace S] : Measurable (constPrefix S) :=
  measurable_pi_iff.mpr fun _ => measurable_id

noncomputable def trajLaw (κ : (n : ℕ) → Kernel ((i : ↥(Finset.Iic n)) → S) S)
    [∀ n, IsMarkovKernel (κ n)] (init : Measure S) : Measure (ℕ → S) :=
  ProbabilityTheory.Kernel.traj (X := fun _ : ℕ => S) κ 0 ∘ₘ (init.map (constPrefix S))

example (κ : (n : ℕ) → Kernel ((i : ↥(Finset.Iic n)) → S) S) [∀ n, IsMarkovKernel (κ n)]
    (init : Measure S) [IsProbabilityMeasure init] : IsProbabilityMeasure (trajLaw κ init) := by
  unfold trajLaw
  infer_instance

end Law

/-! ## B. `Filtration.natural` —— 前提到底有多强 -/

section NaturalFiltration

example : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → ℝ)) :=
  @Filtration.natural _ ℕ _ (fun _ : ℕ => ℝ)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => inferInstance) _ (fun (i : ℕ) (ω : ℕ → ℝ) => ω i)
    (fun i => Measurable.stronglyMeasurable (measurable_pi_apply i))

end NaturalFiltration

/-! ## C. 手写滤子 —— 任意 `[MeasurableSpace S]` 的兜底 -/

section HandFiltration

variable {S : Type*} [MeasurableSpace S]

noncomputable def handFiltration : Filtration ℕ (inferInstance : MeasurableSpace (ℕ → S)) where
  seq i := ⨆ j ≤ i, MeasurableSpace.comap (fun ω : ℕ → S => ω j) inferInstance
  mono' _ _ hij := biSup_mono fun _ => ge_trans hij
  le' _ := iSup₂_le fun j _ => (measurable_pi_apply j).comap_le

end HandFiltration

/-! ## 未做的一件事(记录,不补)

`handFiltration` 与 `Filtration.natural` 在 Borel 情形下 `seq` 体逐字同形
(`natural` 的源码 `.lake/packages/mathlib/Mathlib/Probability/Process/Filtration.lean:396`
是 `seq i := ⨆ j ≤ i, MeasurableSpace.comap (u j) (mβ j)`),因此两者应当定义相等。
**这个相等我没证** —— 它已属证明性陈述,超出本次探针批准的"只答能不能实例化"。
记录在此,供 Lemma 5 之后决定要不要补。 -/

end TSDPP.ProbeTraj
