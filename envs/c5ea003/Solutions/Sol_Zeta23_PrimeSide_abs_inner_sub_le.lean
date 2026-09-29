-- Prove2me | solution 1 for Zeta23.PrimeSide.abs_inner_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T05:25:43.328571+00:00
-- url     : https://prove2.me/submissions/6a999ac8-d0cf-4a7a-94db-e9db6fff4904

import Mathlib
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_PrimeSideA_Basic
import Definitions.Def_Zeta23_PrimeSideA_Defs
import Definitions.Def_Zeta23_PrimeSideB_PPKernel

-- from Zeta23.PrimeSideB.PPKernel
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Part of the Zeta23 formalization of the paper
"More than two thirds of the zeros of the Riemann zeta function lie on the critical line".
-/

/-!
# Kernel lemmas for [prop:PP] (§5.4)

Pure measure-theory / trigonometric-integral / H-MV-application lemmas used by
`Zeta23/PrimeSideB/PP.lean`.

* `sqIntegral_shear`: the substitution `τ = τ' + x` on the square `I×I` (§5.4).
* `intervalIntegral_cos_linear*`: `∫_α^β cos(θt + c) dt` closed forms and the bound `2/|θ|` (§5.4).
-/

noncomputable section

open MeasureTheory Real Set Finset
open scoped BigOperators ArithmeticFunction ComplexConjugate

namespace Zeta23
namespace PrimeSide

/-! ## Elementary facts about the index range `primeRange X = Finset.Ioc 0 ⌊X⌋₊` -/

section Basics











end Basics

/-! ## The shear `(τ,τ') ↦ (x,τ') = (τ−τ',τ')` on `I × I`  (§5.4) -/

section Shear
variable {Φ : ℝ → ℝ} {T : ℝ}




lemma measurableSet_Ix (T x : ℝ) : MeasurableSet (Ix T x) := by
  unfold Ix; exact measurableSet_Icc

lemma mem_Ix {T x τ' : ℝ} : τ' ∈ Ix T x ↔ x + τ' ∈ Icc T (2 * T) ∧ τ' ∈ Icc T (2 * T) := by
  simp only [Ix, Set.mem_Icc, max_le_iff, le_min_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, by linarith⟩, h2, h4⟩
  · rintro ⟨⟨h1, h2⟩, h3, h4⟩; exact ⟨⟨by linarith, h3⟩, by linarith, h4⟩



/-- For `T ≥ 0` the window `I∩(I−x)` is empty unless `|x| ≤ T`; so the `x`-integral may be
restricted to `[−T, T]` (§5.4 "which is empty for |x| ≥ T"). -/
lemma Ix_eq_empty (_hT : 0 ≤ T) {x : ℝ} (hx : T < |x|) : Ix T x = ∅ := by
  unfold Ix
  apply Set.Icc_eq_empty
  intro hle
  have h1 : T - x ≤ 2 * T := le_trans (le_max_left _ _) (hle.trans (min_le_right _ _))
  have h2 : T ≤ 2 * T - x := le_trans (le_max_right _ _) (hle.trans (min_le_left _ _))
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h] at hx; linarith
  · rw [abs_of_neg h] at hx; linarith

/-- On `|x| ≤ T` (and `T ≥ 0`) the window is the honest interval `[max(T−x,T), min(2T−x,2T)]`
with left end ≤ right end, of length `T − |x|`. -/
lemma Ix_le (hT : 0 ≤ T) {x : ℝ} (hx : |x| ≤ T) :
    max (T - x) T ≤ min (2 * T - x) (2 * T) := by
  rw [abs_le] at hx
  simp only [max_le_iff, le_min_iff]; refine ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩

lemma Ix_length {x : ℝ} :
    min (2 * T - x) (2 * T) - max (T - x) T = T - |x| := by
  rcases le_or_gt 0 x with h | h
  · rw [abs_of_nonneg h, min_eq_left (by linarith), max_eq_right (by linarith)]; ring
  · rw [abs_of_neg h, min_eq_right (by linarith), max_eq_left (by linarith)]; ring

end Shear

/-! ## The inner `τ'`-integrals:  `∫_α^β cos(θt + c) dt`  (§5.4) -/

section CosIntegral









variable {T : ℝ}


end CosIntegral

/-! ## Per-frequency-pair decomposition of `𝓜[cos(·y), cos(·y')]`  ([eq:MPP], §5.4) -/

section PairDecomp
variable {Φ : ℝ → ℝ} {T : ℝ}






/-! ### The diagonal 𝒟 (§5.4) -/



/-! ### The sum-frequency terms 𝒪₂ (§5.4) -/


/-! ### The difference-frequency terms 𝒪₁, exact evaluation (§5.4) -/






end PairDecomp

/-! ## Applying H-MV on the prime-power frequencies  ([lem:MV], [eq:deltan]; §5.1, §5.4) -/

section MVapply
variable {C : ℝ}





end MVapply

end PrimeSide
end Zeta23
end
end

-- from Zeta23.PrimeSideA.MuMu
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/PrimeSideA/MuMu.lean

[prop:mumu] (paper §5.4): 𝓜[μ,μ] = 2πbL ∫_T^{2T} μ² + O(l² log L).

Paper proof, as implemented here:
  * shear τ = τ' + x (`sqIntegral_shear`):
      𝓜[μ,μ] = ∫_ℝ Φ(x)² (∫_{I∩(I−x)} μ(x+τ')μ(τ') dτ') dx;
  * Lipschitz step "μ(τ)=μ(τ')+O(|τ−τ'|/T)" (via `mu_increment_bound`'s (K|r|+10r²)/t):
      |∫_{Ix}(μ(x+τ')−μ(τ'))μ(τ')| ≤ l(K|x| + 10x²)   (window length ≤ T, τ' ≥ T);
  * completing ∫_{Ix} to ∫_I ("∫_{I−τ'}Φ² = 2πbL − tails"):
      |∫_{I∖Ix} μ²| ≤ l²·|x|   (vol(I∖Ix) = min(|x|,T));
  * ∫Φ²|x| ≤ 8 + 8log(cϱL/4w) ≪ log L  [eq:psiints]  and  ∫Φ²x² ≤ 8 + 2(cϱ/w)² = O(1).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

open MeasureTheory Real Set
open scoped BigOperators

namespace Zeta23
namespace PrimeSide

variable {cϱ : ℝ}

section Core

variable {p : Setting} {F : LocalFun}



end Core

/-! ## [prop:mumu] -/

variable (cϱ lam : ℝ)


end PrimeSide
end Zeta23
end
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Real Set
open scoped BigOperators
open Zeta23
open PrimeSide
variable {cϱ : ℝ}
variable {p : Setting} {F : LocalFun}

theorem solution (hΓ : Zeta23.GammaFacts) (hF : LocalHypsCore cϱ p F) (hT2 : 2 ≤ p.T)
    (hμl : ∀ τ ∈ Icc p.T (2 * p.T), |Zeta23.mu τ| ≤ p.l)
    {K : ℝ} (hK0 : 0 ≤ K)
    (hKinc : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ,
      |Zeta23.mu (t + r) - Zeta23.mu t| ≤ (K * |r| + 10 * r ^ 2) / t)
    (x : ℝ) :
    |(∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ')
        - ∫ τ' in Icc p.T (2 * p.T), Zeta23.mu τ' ^ 2|
      ≤ (1 + K) * p.l ^ 2 * |x| + 10 * p.l * x ^ 2 := by
  have hμc : Continuous Zeta23.mu := hΓ.smooth.continuous
  have hT0 : (0 : ℝ) < p.T := by linarith
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hl0 : (0 : ℝ) ≤ p.l := by linarith
  have hcnn : 0 ≤ ∫ τ' in Icc p.T (2 * p.T), Zeta23.mu τ' ^ 2 :=
    setIntegral_nonneg measurableSet_Icc fun τ' _ => sq_nonneg _
  have hsq_bound : ∀ τ' ∈ Icc p.T (2 * p.T), ‖Zeta23.mu τ' ^ 2‖ ≤ p.l ^ 2 := by
    intro τ' hτ'
    have h := hμl τ' hτ'
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (Zeta23.mu τ'), sq_abs (Zeta23.mu τ')]
  have hcle : ∫ τ' in Icc p.T (2 * p.T), Zeta23.mu τ' ^ 2 ≤ p.l ^ 2 * p.T := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc p.T (2 * p.T))
      (f := fun τ' => Zeta23.mu τ' ^ 2)
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top) hsq_bound
    rw [Real.norm_eq_abs, abs_of_nonneg hcnn, measureReal_def, Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith), show 2 * p.T - p.T = p.T by ring] at h
    exact h
  rcases le_or_gt |x| p.T with hx | hx
  · -- |x| ≤ T
    have hIle : max (p.T - x) p.T ≤ min (2 * p.T - x) (2 * p.T) := Ix_le hT0.le hx
    have hlen : min (2 * p.T - x) (2 * p.T) - max (p.T - x) p.T = p.T - |x| :=
      Ix_length
    have hIxI : Ix p.T x ⊆ Icc p.T (2 * p.T) := fun τ' hτ' => (mem_Ix.mp hτ').2
    have hIxcompact : IsCompact (Ix p.T x) := by unfold Ix; exact isCompact_Icc
    have hIxmeas : MeasurableSet (Ix p.T x) := measurableSet_Ix p.T x
    have hIxfin : volume (Ix p.T x) ≠ ⊤ := by
      unfold Ix; rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
    have hIxvol : (volume : Measure ℝ).real (Ix p.T x) = p.T - |x| := by
      unfold Ix
      rw [measureReal_def, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
      linarith
    have hIxInt1 : IntegrableOn (fun τ' => Zeta23.mu (x + τ') * Zeta23.mu τ') (Ix p.T x) :=
      ContinuousOn.integrableOn_compact hIxcompact (by fun_prop)
    have hIxInt2 : IntegrableOn (fun τ' => Zeta23.mu τ' ^ 2) (Ix p.T x) :=
      ContinuousOn.integrableOn_compact hIxcompact (by fun_prop)
    have hIInt2 : IntegrableOn (fun τ' => Zeta23.mu τ' ^ 2) (Icc p.T (2 * p.T)) :=
      ContinuousOn.integrableOn_compact isCompact_Icc (by fun_prop)
    -- Lipschitz piece
    have hlip : |(∫ τ' in Ix p.T x, Zeta23.mu (x + τ') * Zeta23.mu τ')
        - ∫ τ' in Ix p.T x, Zeta23.mu τ' ^ 2| ≤ p.l * (K * |x| + 10 * x ^ 2) := by
      rw [← integral_sub hIxInt1 hIxInt2]
      have hb : ∀ τ' ∈ Ix p.T x,
          ‖Zeta23.mu (x + τ') * Zeta23.mu τ' - Zeta23.mu τ' ^ 2‖
            ≤ (K * |x| + 10 * x ^ 2) / p.T * p.l := by
        intro τ' hτ'
        obtain ⟨_, hmem2⟩ := mem_Ix.mp hτ'
        have hτT : p.T ≤ τ' := hmem2.1
        have h2τ : 2 ≤ τ' := by linarith
        have hinc := hKinc τ' h2τ x
        rw [show τ' + x = x + τ' by ring] at hinc
        have hμτ : |Zeta23.mu τ'| ≤ p.l := hμl τ' hmem2
        have hq : (K * |x| + 10 * x ^ 2) / τ' ≤ (K * |x| + 10 * x ^ 2) / p.T := by
          gcongr
        calc ‖Zeta23.mu (x + τ') * Zeta23.mu τ' - Zeta23.mu τ' ^ 2‖
            = |Zeta23.mu (x + τ') - Zeta23.mu τ'| * |Zeta23.mu τ'| := by
              rw [Real.norm_eq_abs, ← abs_mul]; congr 1; ring
          _ ≤ (K * |x| + 10 * x ^ 2) / p.T * p.l :=
              mul_le_mul (hinc.trans hq) hμτ (abs_nonneg _) (by positivity)
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ix p.T x)
        (f := fun τ' => Zeta23.mu (x + τ') * Zeta23.mu τ' - Zeta23.mu τ' ^ 2)
        (lt_of_le_of_ne (le_top) hIxfin) hb
      rw [Real.norm_eq_abs, hIxvol] at h
      refine h.trans ?_
      have hfrac : (p.T - |x|) / p.T ≤ 1 := by
        rw [div_le_one hT0]; linarith [abs_nonneg x]
      have hnum : (0 : ℝ) ≤ K * |x| + 10 * x ^ 2 := by positivity
      calc (K * |x| + 10 * x ^ 2) / p.T * p.l * (p.T - |x|)
          = p.l * (K * |x| + 10 * x ^ 2) * ((p.T - |x|) / p.T) := by ring
        _ ≤ p.l * (K * |x| + 10 * x ^ 2) * 1 := by
            have : (0 : ℝ) ≤ p.l * (K * |x| + 10 * x ^ 2) := by positivity
            exact mul_le_mul_of_nonneg_left hfrac this
        _ = p.l * (K * |x| + 10 * x ^ 2) := mul_one _
    -- completion piece
    have hcomp : |(∫ τ' in Ix p.T x, Zeta23.mu τ' ^ 2)
        - ∫ τ' in Icc p.T (2 * p.T), Zeta23.mu τ' ^ 2| ≤ p.l ^ 2 * |x| := by
      rw [abs_sub_comm, ← setIntegral_diff hIxmeas hIInt2 hIxI]
      have hdvol : (volume : Measure ℝ).real (Icc p.T (2 * p.T) \ Ix p.T x) = |x| := by
        have hsub : volume (Icc p.T (2 * p.T) \ Ix p.T x)
            = volume (Icc p.T (2 * p.T)) - volume (Ix p.T x) :=
          measure_diff hIxI hIxmeas.nullMeasurableSet hIxfin
        rw [measureReal_def, hsub]
        unfold Ix
        rw [Real.volume_Icc, Real.volume_Icc,
          ← ENNReal.ofReal_sub _ (by linarith :
            (0 : ℝ) ≤ min (2 * p.T - x) (2 * p.T) - max (p.T - x) p.T),
          ENNReal.toReal_ofReal (by linarith [abs_nonneg x])]
        linarith
      have hb : ∀ τ' ∈ Icc p.T (2 * p.T) \ Ix p.T x, ‖Zeta23.mu τ' ^ 2‖ ≤ p.l ^ 2 :=
        fun τ' hτ' => hsq_bound τ' hτ'.1
      have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
        (s := Icc p.T (2 * p.T) \ Ix p.T x) (f := fun τ' => Zeta23.mu τ' ^ 2)
        (lt_of_le_of_lt (measure_mono Set.diff_subset)
          (by rw [Real.volume_Icc]; exact ENNReal.ofReal_lt_top)) hb
      rw [Real.norm_eq_abs, hdvol] at h
      exact h
    refine (abs_sub_le _ (∫ τ' in Ix p.T x, Zeta23.mu τ' ^ 2) _).trans ?_
    refine (add_le_add hlip hcomp).trans ?_
    nlinarith [abs_nonneg x, sq_nonneg x,
      mul_nonneg (mul_nonneg hK0 hl0) (abs_nonneg x),
      mul_nonneg (mul_nonneg hK0 (mul_nonneg hl0 hl0)) (abs_nonneg x)]
  · -- |x| > T: the window is empty, the main term itself is ≤ l²T ≤ l²|x|
    rw [Ix_eq_empty hT0.le hx, Measure.restrict_empty, integral_zero_measure, zero_sub,
      abs_neg, abs_of_nonneg hcnn]
    refine hcle.trans ?_
    nlinarith [mul_nonneg (sq_nonneg p.l) (by linarith : (0 : ℝ) ≤ |x| - p.T),
      mul_nonneg (mul_nonneg hK0 (sq_nonneg p.l)) (abs_nonneg x),
      mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 10) hl0) (sq_nonneg x)]
