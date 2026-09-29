-- Prove2me | solution 1 for Zeta23.WeilEF.EF_lit_zeta
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:12:28.367349+00:00
-- url     : https://prove2.me/submissions/8b1faa15-1771-44ec-b417-042a6517f8fa

import Batteries.Tactic.Lemma
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.LogDerivUniformlyOn
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.IntegerCompl
import Mathlib.Analysis.Complex.ReImTopology
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Fourier.Convolution
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Cast.OfScientific
import Mathlib.Data.Real.StarOrdered
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Order.Group.Lattice
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Order.Interval.Set.Monotone
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombinationPrime
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Analytic_RectangleLogDeriv
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_ExplicitFormula
import Definitions.Def_Zeta23_FromPNTPlus_EulerMaclaurin
import Definitions.Def_Zeta23_FromPNTPlus_Fourier
import Definitions.Def_Zeta23_FromPNTPlus_Rectangle
import Definitions.Def_Zeta23_FromPNTPlus_ResidueCalcOnRectangles
import Definitions.Def_Zeta23_FromPNTPlus_Sobolev
import Definitions.Def_Zeta23_FromPNTPlus_StrongPNTPrefix
import Definitions.Def_Zeta23_FromPNTPlus_ZetaBounds
import Definitions.Def_Zeta23_GammaFacts_Series
import Definitions.Def_Zeta23_GammaFacts_StirlingVert
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_RvM_LocalCount
import Definitions.Def_Zeta23_Statement
import Definitions.Def_Zeta23_Statement_Seam
import Definitions.Def_Zeta23_Statement_SeamClosed
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne
import Definitions.Def_Zeta23_WeilEF_FullLine
import Definitions.Def_Zeta23_WeilEF_VerticalLine
import Definitions.Def_Zeta23_WeilEF_ZeroSummability
import Definitions.Def_Zeta23_ZetaReflect
import Definitions.Def_Extra_Zeta23_Analytic_RectangleLogDeriv
import Theorems.Thm_Zeta23_RvM_zeta_local_zero_count
import Theorems.Thm_Zeta23_WeilEF_EF_zero_sum_summable_gen
import Theorems.Thm_Zeta23_WeilEF_Hfn_mirror
import Theorems.Thm_Zeta23_WeilEF_continuous_logDeriv_zeta_line
import Theorems.Thm_Zeta23_WeilEF_differentiableAt_GammaR
import Theorems.Thm_Zeta23_WeilEF_differentiable_paperFT
import Theorems.Thm_Zeta23_WeilEF_full_line_identity
import Theorems.Thm_Zeta23_WeilEF_gammaR_bracket
import Theorems.Thm_Zeta23_WeilEF_gamma_line_shift
import Theorems.Thm_Zeta23_WeilEF_integrable_mul_logDeriv_GammaR_of_decay
import Theorems.Thm_Zeta23_WeilEF_norm_Hfn_le
import Theorems.Thm_Zeta23_WeilEF_norm_logDeriv_zeta_le_of_one_lt_re
import Theorems.Thm_Zeta23_WeilEF_prime_side_line

-- from Zeta23.Statement
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Statement.lean — the statement layer.

Canonical text: the paper, §1 [Results], [eq:trivialchain], [thm:A], [thm:B], [thm:C].

It (1) defines nontrivial zeros, multiplicity (via analyticOrderAt) and the six counting functions of
§1 directly against Mathlib; (2) packages the "seam" facts needed to view them as an abstract
Zeta23.ZeroConfig (structure ZetaSeam — classical facts about ζ, established from Mathlib elsewhere in
the repository, not paper inputs); (3) states Theorems A, B, C in ε-form (fixed λ ∈ (0,1) with
constant H(λ), F(λ), then the 2/3, 1/2, 3/4 liminf wrappers via λ → 1⁻);
(4) proves the sanity anchors connecting to Mathlib's RiemannHypothesis and [eq:trivialchain].
-/

open scoped BigOperators ComplexConjugate
open Complex Set

noncomputable section

namespace Zeta23

/-! ## 1. Nontrivial zeros and multiplicity, against Mathlib -/










/-! ## 2. The seam: ζ's zeros as an abstract ZeroConfig -/



section seam_rfl
variable (hs : ZetaSeam) (T₁ T₂ : ℝ)

@[simp] lemma zetaZeros_carrier : (zetaZeros hs).carrier = {ρ | IsNontrivialZero ρ} := rfl
@[simp] lemma zetaZeros_mult : (zetaZeros hs).mult = zeroMult := rfl
@[simp] lemma zetaZeros_simple : (zetaZeros hs).simple = {ρ | zeroMult ρ = 1} := rfl

lemma zetaZeros_window : (zetaZeros hs).window T₁ T₂ = zerosIn T₁ T₂ := by
  ext ρ; simp [ZeroConfig.window, zerosIn]

@[simp] lemma zetaZeros_N : (zetaZeros hs).N T₁ T₂ = Ncount T₁ T₂ := by
  simp [ZeroConfig.N, Ncount, zetaZeros_window]
@[simp] lemma zetaZeros_Nd : (zetaZeros hs).Nd T₁ T₂ = Ndist T₁ T₂ := by
  simp [ZeroConfig.Nd, Ndist, zetaZeros_window]
@[simp] lemma zetaZeros_N0 : (zetaZeros hs).N0 T₁ T₂ = N0 T₁ T₂ := by
  simp [ZeroConfig.N0, N0, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_N0star : (zetaZeros hs).N0star T₁ T₂ = N0star T₁ T₂ := by
  simp [ZeroConfig.N0star, N0star, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_N0s : (zetaZeros hs).N0s T₁ T₂ = N0simple T₁ T₂ := by
  simp [ZeroConfig.N0s, N0simple, zetaZeros_window, ZeroConfig.onLine]
@[simp] lemma zetaZeros_Ns : (zetaZeros hs).Ns T₁ T₂ = Nsimple T₁ T₂ := by
  simp [ZeroConfig.Ns, Nsimple, zetaZeros_window]

end seam_rfl

/-! ## 3. Sanity anchors (connection to Mathlib's existing statement of RH) -/





/-! ## 4. Theorems A, B, C

The headline theorems Zeta23.thmA, thmA_cumulative, thmA_lam, thmB, thmB_cumulative, thmB_lam, thmC,
thmC_cumulative, thmC_lam are proved in Zeta23/Final.lean (their types display the full trust base:
literature explicit formula, Riemann–von Mangoldt, Montgomery–Vaughan, Γ-facts), on top of the
versions Zeta23.thmA_of_traces etc. in Zeta23/Main.lean (thm:traces as an explicit hypothesis). This file
stays light (definitions + anchors) so that it can be read and imported cheaply.

Paper [thm:A], verbatim: "Let 0 < λ ≤ 1 be fixed. There are constants c(λ) > 0 and T₀(λ) such that
for all T ≥ T₀(λ)   N₀*(T,2T) ≥ (H(λ) − c(λ) loglogT/logT) N(T,2T),
and for λ < 1 the factor loglog T may be omitted. In particular
  liminf_{T→∞} N₀*(T,2T)/N(T,2T) ≥ 2/3,   liminf_{T→∞} N₀*(T)/N(T) ≥ 2/3".
Formal target: the ε-forms, for each fixed λ ∈ (0,1) with constant
H(λ) (resp. 2F(λ)−1, F(λ)), which absorb c(λ)/log T; then the 2/3 (resp. 1/2, 3/4) forms via
sup_{λ<1} H(λ) = H(1) = 2/3 etc. The effective c(λ) forms are not stated. -/




end Zeta23
end
end

-- from Zeta23.ExplicitFormula.Bridge
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ExplicitFormula/Bridge.lean

The two "all integrals absolutely convergent" side-facts of App. A [app:EF]:
  * `integrable_fourier_of_contDiff_two` : k ∈ C_c²(ℝ) ⇒ 𝓕 k ∈ L¹(ℝ)   (from [eq:hfbound], Zeta23/Poisson/PaperFT.lean);
  * `integrable_paperFT_mul_mu`          : k ∈ C_c²(ℝ) ⇒ h_k · μ ∈ L¹(ℝ)  (from [eq:hfbound] + H-Γ [eq:mufacts]);
and the clean bridge
  * `explicitFormulaPaper_of_lit` : EF_lit Z → GammaFacts → ExplicitFormulaPaper Z,
i.e. the literature-form explicit formula [eq:EFstd] (plus the Stirling facts for μ that PaperInputs already
carries) implies the paper's [prop:EF]/[eq:EF] exactly as Hypotheses.lean states it.
-/

open MeasureTheory Complex Filter Set
open scoped Real FourierTransform ComplexConjugate

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Zeta23
namespace EF

/-- A compactly supported function on ℝ is supported in some `[−Λ, Λ]`. -/
theorem exists_abs_le_of_hasCompactSupport {k : ℝ → ℂ} (hkc : HasCompactSupport k) :
    ∃ Λ : ℝ, ∀ u, k u ≠ 0 → |u| ≤ Λ := by
  obtain ⟨R, hR⟩ := hkc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun u hu => ?_⟩
  have := hR (subset_tsupport _ (Function.mem_support.mpr hu))
  simpa [Real.norm_eq_abs] using this








end EF
end Zeta23
end
end

-- from Zeta23.WeilEF.XiLogDeriv
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/XiLogDeriv.lean
The completed zeta function Λ = completedRiemannZeta: log-derivative decomposition, functional equation
for logDeriv, zeros in the strip = nontrivial zeros of ζ with equal analytic order.

Mathlib normalization (verified): for s ≠ 0, riemannZeta s = completedRiemannZeta s / Gammaℝ s
(riemannZeta_def_of_ne_zero) and Gammaℝ s ≠ 0 for 0 < Re s (Gammaℝ_ne_zero_of_re_pos); hence on the
open right half-plane Λ = Γℝ · ζ on the nose (completedZeta_eventuallyEq_mul) — no pole bookkeeping is
needed for the three statements below (Λ's poles at 0, 1 are excluded by hypothesis).
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Filter Topology



/-- On the right half-plane, Λ = Γℝ · ζ (as germs). -/
lemma completedZeta_eventuallyEq_mul {s : ℂ} (hs : 0 < s.re) :
    completedRiemannZeta =ᶠ[𝓝 s] fun u => Gammaℝ u * riemannZeta u := by
  have hopen : IsOpen {u : ℂ | 0 < u.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds hs] with u hu
  have hu0 : u ≠ 0 := fun h0 => by simp [h0] at hu
  have hΓ := Gammaℝ_ne_zero_of_re_pos hu
  rw [riemannZeta_def_of_ne_zero hu0]
  field_simp


/-- On the right half-plane away from 1 and from the zeros of ζ:  Λ'/Λ = Γℝ'/Γℝ + ζ'/ζ. -/
theorem logDeriv_completedZeta (s : ℂ) (hs1 : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) (hstrip : 0 < s.re) :
    logDeriv completedRiemannZeta s = logDeriv Complex.Gammaℝ s + logDeriv riemannZeta s := by
  have hev := completedZeta_eventuallyEq_mul hstrip
  have heq : logDeriv completedRiemannZeta s = logDeriv (fun u => Gammaℝ u * riemannZeta u) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  rw [heq]
  exact logDeriv_mul s (Gammaℝ_ne_zero_of_re_pos hstrip) hζ (differentiableAt_GammaR hstrip)
    (differentiableAt_riemannZeta hs1)



end WeilEF
end Zeta23
end
end

-- from Zeta23.WeilEF.ZeroSummability
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Set Filter MeasureTheory

/-! ### γ_ρ bookkeeping -/






/-! ### The weight series Σ_{n∈ℤ} log(|n|+3)/(1+n²) -/




/-! ### zero_sum_inv_sq -/





/-! ### The generic theorems (any ZeroConfig with the local count) -/




/-! ### The ζ instances -/


/-! ### EF_zero_sum_summable -/

/-- The EF zero-side sum converges absolutely for every k ∈ C_c²(ℝ)
(via [eq:hfbound]: ‖h(γ_ρ)‖ ≤ e^{Λ/2}‖k''‖₁/‖γ_ρ‖², |Im γ_ρ| < 1/2) — EF_lit's Summable clause. -/
theorem EF_zero_sum_summable (hs : ZetaSeam) {k : ℝ → ℂ}
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : (zetaZeros hs).carrier =>
      ((zetaZeros hs).mult ρ : ℂ) * paperFT k (gammaOf ρ)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := Zeta23.RvM.zeta_local_zero_count
  exact EF_zero_sum_summable_gen (zetaZeros hs) hA₀ (fun t => by rw [zetaZeros_N]; exact hloc t) hk hkc

end WeilEF
end Zeta23
end
end

-- from Zeta23.WeilEF.FullLine
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/FullLine.lean — the R → ∞ limit of the rectangle identity
(Zeta23.WeilEF.rectangle_identity, proved): along good heights R_j ∈ [j, j+1] the horizontal
sides vanish (‖H‖ ≪_k 1/R², ‖Λ'/Λ‖ ≪ log²j on them, reflecting Λ'/Λ(1−s) = −Λ'/Λ(s) for
re s < 1/2), the vertical sides converge to the full-line integral (dominated convergence; the
left side is folded onto the right by the functional equation and t ↦ −t), and the zero sums
over |γ| < R_j converge to the absolutely convergent tsum (EF_zero_sum_summable).  The
resulting statement is consumed by Zeta23/WeilEF/Main.lean.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex Topology Filter Set MeasureTheory
open scoped ArithmeticFunction

/-! ## Majorant pack -/

section Majorants



/-- `H` is continuous along vertical lines (indeed paperFT k is entire). -/
theorem continuous_Hfn_line {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) (σ : ℝ) :
    Continuous (fun t : ℝ => Hfn k ((σ : ℂ) + t * I)) := by
  have h := (differentiable_paperFT hk.continuous hkc).continuous
  unfold Hfn
  exact h.comp (by fun_prop)



/-- generic: a continuous `φ` with `‖φ(t)‖ ≤ C/(1+t²)` times `ζ'/ζ(c+it)` is integrable. -/
theorem integrable_mul_logDeriv_zeta_of_decay {φ : ℝ → ℂ} (hφc : Continuous φ) {C : ℝ}
    (hφ : ∀ t, ‖φ t‖ ≤ C / (1 + t ^ 2)) {c : ℝ} (hc1 : 1 < c) :
    Integrable (fun t : ℝ => φ t * logDeriv riemannZeta ((c : ℂ) + t * I)) := by
  obtain ⟨M, hM0, hM⟩ := norm_logDeriv_zeta_le_of_one_lt_re hc1
  have hC0 : 0 ≤ C := by
    have := le_trans (norm_nonneg _) (hφ 0); simpa using this
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul (C * M)))
    (hφc.mul (continuous_logDeriv_zeta_line hc1)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  rw [norm_mul]
  calc ‖φ t‖ * ‖logDeriv riemannZeta ((c : ℂ) + t * I)‖
      ≤ (C / (1 + t ^ 2)) * M := mul_le_mul (hφ t) (hM t) (norm_nonneg _) (by positivity)
    _ = C * M * (1 + t ^ 2)⁻¹ := by ring

/-- **Integrability of `H(c+it)·ζ'/ζ(c+it)`** on `re = c ∈ (1, 3/2]`. -/
theorem integrable_Hfn_mul_logDeriv_zeta {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {c : ℝ} (hc1 : 1 < c) (hc2 : c ≤ 3 / 2) :
    Integrable (fun t : ℝ => Hfn k ((c : ℂ) + t * I) * logDeriv riemannZeta ((c : ℂ) + t * I)) := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  exact integrable_mul_logDeriv_zeta_of_decay (continuous_Hfn_line hk hkc c)
    (fun t => hC c t (by linarith) (by linarith)) hc1




/-- **Integrability of `H(σ+it)·Γℝ'/Γℝ(σ+it)`** for `1/2 ≤ σ ≤ 3/2`. -/
theorem integrable_Hfn_mul_logDeriv_Gammaℝ {k : ℝ → ℂ} (hk : ContDiff ℝ 2 k)
    (hkc : HasCompactSupport k) {σ : ℝ} (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 3 / 2) :
    Integrable (fun t : ℝ => Hfn k ((σ : ℂ) + t * I) * logDeriv Complex.Gammaℝ ((σ : ℂ) + t * I)) := by
  obtain ⟨C, hC0, hC⟩ := norm_Hfn_le hk hkc
  exact integrable_mul_logDeriv_GammaR_of_decay (continuous_Hfn_line hk hkc σ) hC0
    (fun t => hC σ t (by linarith) (by linarith)) hσ1 hσ2

end Majorants

/-! ## Good heights (indexed so that no side conditions remain: R_j ∈ [j+7, j+8]) -/

section Heights


end Heights

/-! ## The vertical sides -/

section Verticals

variable {k : ℝ → ℂ}








end Verticals

end WeilEF
end Zeta23
end
end

-- from Zeta23.WeilEF.Main
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/WeilEF/Main.lean — Final assembly: EF_lit for the concrete ζ zero configuration.
-/

noncomputable section

namespace Zeta23
namespace WeilEF

open Complex MeasureTheory
open scoped ArithmeticFunction





end WeilEF
end Zeta23
end
open Zeta23
open WeilEF
open Complex MeasureTheory
open scoped ArithmeticFunction

theorem solution (hs : ZetaSeam) : Zeta23.EF.EF_lit (zetaZeros hs) := by
  intro k hk hkc
  refine ⟨EF_zero_sum_summable hs hk hkc, ?_⟩
  -- Fix c := 5/4; split LΛ = LΓℝ + Lζ on the line; evaluate the three parts; rearrange.
  have h54a : (1:ℝ) < 5/4 := by norm_num
  have h54b : (5/4:ℝ) ≤ 3/2 := by norm_num
  have hkneg2 : ContDiff ℝ 2 (fun u : ℝ => k (-u)) := hk.comp contDiff_neg
  have hknegc : HasCompactSupport (fun u : ℝ => k (-u)) := by
    have := hkc.comp_homeomorph (Homeomorph.neg ℝ)
    exact this
  have hfull := full_line_identity hs hk hkc h54a h54b
  -- pointwise split of Λ'/Λ on the line Re = 5/4
  have hsne : ∀ t : ℝ, ((5/4:ℝ) : ℂ) + t * I ≠ 0 ∧ ((5/4:ℝ) : ℂ) + t * I ≠ 1
      ∧ riemannZeta (((5/4:ℝ) : ℂ) + t * I) ≠ 0 ∧ 0 < ((((5/4:ℝ) : ℂ)) + t * I).re := by
    intro t
    have hre : ((((5/4:ℝ) : ℂ)) + t * I).re = 5/4 := by simp
    refine ⟨fun h => ?_, fun h => ?_, riemannZeta_ne_zero_of_one_lt_re (by rw [hre]; norm_num), by
      rw [hre]; norm_num⟩
    · rw [h] at hre
      simp at hre
      linarith
    · rw [h] at hre
      simp at hre
      linarith
  have hsplit : ∀ t : ℝ, logDeriv completedRiemannZeta (((5/4:ℝ):ℂ) + t * I)
      = logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I)
        + logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I) := by
    intro t
    obtain ⟨h0, h1, hζ, hpos⟩ := hsne t
    exact logDeriv_completedZeta _ h1 hζ hpos
  -- notation
  have hH2eq : ∀ t : ℝ, Hfn k (1 - (5/4:ℝ) - t * I)
      = Hfn (fun u => k (-u)) (((5/4:ℝ):ℂ) + t * I) := fun t => Hfn_mirror k (5/4) t
  -- integrability of the ζ-parts
  have hint1 : Integrable (fun t : ℝ => Hfn k (((5/4:ℝ):ℂ) + t * I)
      * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)) :=
    integrable_Hfn_mul_logDeriv_zeta hk hkc h54a h54b
  have hint2 : Integrable (fun t : ℝ => Hfn k (1 - (5/4:ℝ) - t * I)
      * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)) := by
    have heq : (fun t : ℝ => Hfn k (1 - (5/4:ℝ) - t * I)
        * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I))
        = fun t : ℝ => Hfn (fun u => k (-u)) (((5/4:ℝ):ℂ) + t * I)
          * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I) := by
      funext t
      rw [hH2eq t]
    rw [heq]
    exact integrable_Hfn_mul_logDeriv_zeta hkneg2 hknegc h54a h54b
  have hintζ : Integrable (fun t : ℝ => (Hfn k (((5/4:ℝ):ℂ) + t * I)
      + Hfn k (1 - (5/4:ℝ) - t * I)) * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)) := by
    refine (hint1.add hint2).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]
    ring
  -- integrability of the Γℝ-part
  have hintΓ1 : Integrable (fun t : ℝ => Hfn k (((5/4:ℝ):ℂ) + t * I)
      * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I)) :=
    integrable_Hfn_mul_logDeriv_Gammaℝ hk hkc (by norm_num) (by norm_num)
  have hintΓ2 : Integrable (fun t : ℝ => Hfn k (1 - (5/4:ℝ) - t * I)
      * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I)) := by
    have heq : (fun t : ℝ => Hfn k (1 - (5/4:ℝ) - t * I)
        * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I))
        = fun t : ℝ => Hfn (fun u => k (-u)) (((5/4:ℝ):ℂ) + t * I)
          * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I) := by
      funext t
      rw [hH2eq t]
    rw [heq]
    exact integrable_Hfn_mul_logDeriv_Gammaℝ hkneg2 hknegc (σ := 5/4) (by norm_num) (by norm_num)
  have hintΓ : Integrable (fun t : ℝ => (Hfn k (((5/4:ℝ):ℂ) + t * I)
      + Hfn k (1 - (5/4:ℝ) - t * I)) * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I)) := by
    refine (hintΓ1.add hintΓ2).congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [Pi.add_apply]
    ring
  -- split the full-line integral
  have hsplitint : (∫ t : ℝ, (Hfn k (((5/4:ℝ):ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
        * logDeriv completedRiemannZeta (((5/4:ℝ):ℂ) + t * I))
      = (∫ t : ℝ, (Hfn k (((5/4:ℝ):ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
          * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I))
        + ∫ t : ℝ, (Hfn k (((5/4:ℝ):ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
          * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I) := by
    rw [← integral_add hintΓ hintζ]
    congr 1
    funext t
    show (Hfn k (((5/4:ℝ):ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
      * logDeriv completedRiemannZeta (((5/4:ℝ):ℂ) + t * I) = _
    rw [hsplit t]
    ring
  -- ζ-part evaluation via prime_side_line (both lines)
  have hζ1 : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k (((5/4:ℝ):ℂ) + t * I)
      * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)
      = -∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n) := by
    have h := prime_side_line hk hkc h54a
    have h2 : (∫ t : ℝ, Hfn k (((5/4:ℝ):ℂ) + t * I)
        * (-logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)))
        = -∫ t : ℝ, Hfn k (((5/4:ℝ):ℂ) + t * I)
          * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I) := by
      rw [← integral_neg]
      congr 1
      funext t
      ring
    rw [h2] at h
    linear_combination -h
  have hζ2 : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, Hfn k (1 - (5/4:ℝ) - t * I)
      * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)
      = -∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (-Real.log n) := by
    have h := prime_side_line hkneg2 hknegc h54a
    have h2 : (∫ t : ℝ, Hfn (fun u => k (-u)) (((5/4:ℝ):ℂ) + t * I)
        * (-logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I)))
        = -∫ t : ℝ, Hfn k (1 - (5/4:ℝ) - t * I)
          * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I) := by
      rw [← integral_neg]
      congr 1
      funext t
      rw [hH2eq t]
      ring
    rw [h2] at h
    have h3 : (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (fun u => k (-u)) (Real.log n))
        = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (-Real.log n) := rfl
    rw [h3] at h
    linear_combination -h
  -- Γ-part evaluation
  have hΓeval : (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, (Hfn k (((5/4:ℝ):ℂ) + t * I)
      + Hfn k (1 - (5/4:ℝ) - t * I)) * logDeriv Complex.Gammaℝ (((5/4:ℝ):ℂ) + t * I)
      = (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * ((Zeta23.EF.gammaBracket r : ℝ) : ℂ) := by
    congr 1
    rw [gamma_line_shift hk hkc h54a h54b]
    congr 1
    funext t
    rw [gammaR_bracket t]
    congr 2
    unfold Zeta23.EF.gammaBracket
    congr 3
    ring
  -- pole values
  have hpole0 : Hfn k 0 = paperFT k (I / 2) := by
    unfold Hfn
    congr 1
    rw [div_eq_iff Complex.I_ne_zero, div_mul_eq_mul_div, Complex.I_mul_I]
    norm_num
  have hpole1 : Hfn k 1 = paperFT k (-I / 2) := by
    unfold Hfn
    congr 1
    rw [div_eq_iff Complex.I_ne_zero]
    rw [show (-I / 2) * I = -(I * I) / 2 by ring, Complex.I_mul_I]
    norm_num
  -- summability of the two prime sums (finite support)
  obtain ⟨B₁, hB₁⟩ := Zeta23.EF.exists_abs_le_of_hasCompactSupport hkc
  have hsummable_gen : ∀ (g : ℝ → ℂ), (∀ u, g u ≠ 0 → |u| ≤ max B₁ 0) →
      Summable (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * g (Real.log n)) := by
    intro g hg
    refine summable_of_hasFiniteSupport ?_
    have hsub : Function.support (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * g (Real.log n))
        ⊆ Set.Iic ⌈Real.exp (max B₁ 0)⌉₊ := by
      intro n hn
      rw [Function.mem_support] at hn
      have hgne : g (Real.log n) ≠ 0 := by
        intro h
        rw [h, mul_zero] at hn
        exact hn rfl
      have hlog := hg _ hgne
      have hn0 : n ≠ 0 := by
        rintro rfl
        simp at hn
      have hn1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0
      have : (n:ℝ) ≤ Real.exp (max B₁ 0) := by
        have h2 : Real.log n ≤ max B₁ 0 := (le_abs_self _).trans hlog
        calc (n:ℝ) = Real.exp (Real.log n) := (Real.exp_log (by linarith)).symm
          _ ≤ Real.exp (max B₁ 0) := Real.exp_le_exp.mpr h2
      rw [Set.mem_Iic]
      exact_mod_cast this.trans (Nat.le_ceil _)
    exact (Set.finite_Iic _).subset hsub
  have hsummable1 : Summable (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n)) :=
    hsummable_gen k (fun u hu => (hB₁ u hu).trans (le_max_left _ _))
  have hsummable2 : Summable (fun n : ℕ => ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (-Real.log n)) := by
    refine hsummable_gen (fun u => k (-u)) (fun u hu => ?_)
    have h2 := hB₁ (-u) hu
    rw [abs_neg] at h2
    exact h2.trans (le_max_left _ _)
  -- assemble
  have hmerge : (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (Real.log n))
      + (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * k (-Real.log n))
      = ∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
    rw [← Summable.tsum_add hsummable1 hsummable2]
    refine tsum_congr fun n => ?_
    ring
  -- paperFT k (gammaOf ρ) = Hfn k ρ definitionally
  have hgammaOf : ∀ ρ : (zetaZeros hs).carrier,
      paperFT k (gammaOf (ρ : ℂ)) = Hfn k (ρ : ℂ) := fun ρ => rfl
  rw [Zeta23.EF.literatureRHS]
  calc ∑' ρ : (zetaZeros hs).carrier, ((zetaZeros hs).mult ρ : ℂ) * paperFT k (gammaOf (ρ:ℂ))
      = ∑' ρ : (zetaZeros hs).carrier, ((zetaZeros hs).mult ρ : ℂ) * Hfn k (ρ:ℂ) := by
        refine tsum_congr fun ρ => by rw [hgammaOf ρ]
    _ = (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k (((5/4:ℝ):ℂ) + t * I)
          + Hfn k (1 - (5/4:ℝ) - t * I)) * logDeriv completedRiemannZeta (((5/4:ℝ):ℂ) + t * I))
        + Hfn k 0 + Hfn k 1 := by
        rw [hfull]
        ring
    _ = paperFT k (I / 2) + paperFT k (-I / 2)
        - (∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)))
        + (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, paperFT k r * ((Zeta23.EF.gammaBracket r : ℝ) : ℂ) := by
        rw [hsplitint, mul_add, hΓeval, hpole0, hpole1]
        have hζboth : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, (Hfn k (((5/4:ℝ):ℂ) + t * I)
            + Hfn k (1 - (5/4:ℝ) - t * I)) * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I))
            = -∑' n : ℕ, ((Λ n / Real.sqrt n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n)) := by
          have hsum2 : (∫ t : ℝ, (Hfn k (((5/4:ℝ):ℂ) + t * I) + Hfn k (1 - (5/4:ℝ) - t * I))
              * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I))
              = (∫ t : ℝ, Hfn k (((5/4:ℝ):ℂ) + t * I)
                  * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I))
                + ∫ t : ℝ, Hfn k (1 - (5/4:ℝ) - t * I)
                  * logDeriv riemannZeta (((5/4:ℝ):ℂ) + t * I) := by
            rw [← integral_add hint1 hint2]
            congr 1
            funext t
            ring
          rw [hsum2, mul_add, hζ1, hζ2, ← hmerge]
          ring
        rw [hζboth]
        ring
