-- Prove2me | Definitions.Def_AnalyticCombinatorics_Compatibility_TendstoInDistribution
-- name    : AnalyticCombinatorics_Compatibility_TendstoInDistribution
-- status  : Definition
-- author  : @FormallyCorrect
-- created : 2026-10-26T10:30:55.787549+00:00
-- url     : https://prove2.me/theorems/4d4cdf3d-6040-4d26-9036-4f4628ffab91
-- title:
--   Weak convergence on varying probability spaces
-- statement:
--   Let $\iota$ index measurable spaces $\Omega_i$ with probability measures $\mu_i$, and let $\Omega′$ carry a probability measure $\mu′$. For a measurable topological space $E$ with measurable open sets, maps $X_i:\Omega_i\to E$, a limit map $Z:\Omega′\to E$, and a filter $l$, the predicate TendstoInDistribution consists of exactly three fields: every $X_i$ is almost everywhere measurable under $\mu_i$; $Z$ is almost everywhere measurable under $\mu′$; and the image probability measures converge weakly,
--
--   $$\bigl((\mu_i)\circ X_i^{-1}\bigr)\longrightarrow_l\mu′\circ Z^{-1}\quad\text{in }\operatorname{ProbabilityMeasure}(E).$$
--
--   The source probability spaces may depend on the index, and the limit probability space is separate. This is the explicit three-field compatibility predicate used by the preserved theorem contract.
-- source:
--   Canonical definition: https://github.com/leanprover-community/mathlib4/blob/8a178386ffc0f5fef0b77738bb5449d50efeea95/Mathlib/MeasureTheory/Function/ConvergenceInDistribution.lean ; Apache-2.0. Explicit compatibility source in AnalyticCombinatorics.Compatibility.TendstoInDistribution preserves the canonical three-field contract.

import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


open Filter MeasureTheory
open scoped Topology

namespace AnalyticCombinatorics.Compatibility

variable {ι E Ω' : Type*} {Ω : ι → Type*} {m : ∀ i, MeasurableSpace (Ω i)}
  {μ : (i : ι) → Measure (Ω i)} [∀ i, IsProbabilityMeasure (μ i)]
  {m' : MeasurableSpace Ω'} {μ' : Measure Ω'} [IsProbabilityMeasure μ']
  {mE : MeasurableSpace E} [TopologicalSpace E]
  {X Y : (i : ι) → Ω i → E} {Z : Ω' → E} {l : Filter ι}

/-- Convergence in distribution for index-dependent source probability spaces.
This preserves the canonical Mathlib three-field definition, including a separate limit space. -/
structure TendstoInDistribution [OpensMeasurableSpace E] (X : (i : ι) → Ω i → E) (l : Filter ι)
    (Z : Ω' → E) (μ : (i : ι) → Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (μ' : Measure Ω' := by volume_tac) [IsProbabilityMeasure μ'] : Prop where
  forall_aemeasurable : ∀ i, AEMeasurable (X i) (μ i)
  aemeasurable_limit : AEMeasurable Z μ' := by fun_prop
  tendsto : Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨(μ n).map (X n), Measure.isProbabilityMeasure_map (forall_aemeasurable n)⟩) l
      (𝓝 ⟨μ'.map Z, Measure.isProbabilityMeasure_map aemeasurable_limit⟩)

end AnalyticCombinatorics.Compatibility


