-- Prove2me | solution 1 for RLHF.tiltVar_eq_range_sq_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:34:08.679649+00:00
-- url     : https://prove2.me/submissions/53d993fb-e6c4-45ee-8a1f-ee01147a6923

-- Sol generated from NumberTheory/RLHFVarianceSharpness.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFVarianceCurvature
import Definitions.Def_NumberTheory_RLHFVarianceSharpness
import Definitions.Def_NumberTheory_RLHFZetaEulerPolicy
import Theorems.Thm_RLHF_tiltVar_shift
import Theorems.Thm_RLHF_tiltWeight_pos
import Theorems.Thm_RLHF_tiltWeight_sum

/-!
# Sharpness of the alignment speed limit, and curvature of the Euler factors

This file closes two of the three next-cycle sub-conjectures recorded in
`FUTURE_DIRECTIONS.md` after the curvature identity
`RLHF.deriv2_logExpMoment_eq_tiltVar` was proved.

**Sub-conjecture 1 (sharpness of the speed limit).**  `RLHF.tiltVar_le_range_sq` caps the
reward variance of a model confined to `[m, M]` by `(M − m)²/4`, and
`RLHF.tiltMean_drift_le` turns that into a temperature-uniform speed limit for alignment.
Here we show that the constant `1/4` cannot be improved and describe exactly when it is
attained:

* `RLHF.tiltVar_shift` — the variance of the tilted policy computed around an arbitrary
  centre.
* `RLHF.tiltVar_eq_range_sq_iff` — **the equality analysis**: the Popoviciu ceiling is
  attained at a temperature `t` if and only if the reward model is two-valued, taking only
  the extreme values `m` and `M`, *and* the tilted policy splits its mass evenly between the
  two levels (equivalently `𝔼_{π_t}[r] = (m+M)/2`).
* `RLHF.twoAtom_tiltVar`, `RLHF.twoAtom_tiltVar_zero` — the extremal model: the two-atom
  reward `r ∈ {0,1}` with balanced reference has `Var_{π_t}(r) = e^t/(1+e^t)²`, equal to
  `1/4` at `t = 0`.
* `RLHF.popoviciu_constant_sharp` and `RLHF.tiltMean_drift_constant_sharp` — consequently no
  constant below `1/4` can appear either in the variance ceiling or in the drift bound; the
  second statement is a genuine derivative argument (the slope of the logistic alignment
  curve at the origin).

**Sub-conjecture 2 (curvature of the Euler factors).**  The local zeta factor
`localZeta s p A = ∑_{k ≤ A} p^{-ks}` is the RLHF partition function of the reward
`k ↦ −k log p` on the exponent space `{0, …, A}` with uniform reference:

* `RLHF.expMoment_zero_geomReward` — the identification.
* `RLHF.convexOn_logLocalZeta`, `RLHF.strictConvexOn_logLocalZeta` — each Euler factor is
  log-convex in the exponent, strictly so for `p ≥ 2` and `A ≥ 1`.
* `RLHF.localZeta_curvature_eq_variance` — `d²/ds² log localZeta = Var(k log p)` under the
  truncated geometric law on exponents.
* `RLHF.zetaSum_curvature_additive` — **additive curvature decomposition**: the curvature of
  the truncated Euler product is the sum of the per-prime curvatures.  Alignment "difficulty"
  is a sum of independent local contributions.
-/

open RLHF

open Finset Filter Topology

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]

/-! ## 1. Variance around an arbitrary centre -/


/-! ## 2. Equality analysis for the Popoviciu ceiling -/


/-! ## 3. The extremal two-atom model -/















/-! ## 4. Curvature of the Euler factors -/











open RLHF in
theorem solution{r p : Ω → ℝ} (hp : ∀ y, 0 < p y) {m M : ℝ}
    (hm : ∀ y, m ≤ r y) (hM : ∀ y, r y ≤ M) (t : ℝ) :
    tiltVar r p t = (M - m) ^ 2 / 4 ↔
      ((∀ y, r y = m ∨ r y = M) ∧ tiltMean r p t = (m + M) / 2) := by
  set a := (m + M) / 2 with ha
  have hkey := tiltVar_shift (r := r) hp a t
  have hw := tiltWeight_pos (r := r) hp t
  have hsum := tiltWeight_sum (r := r) hp t
  constructor
  · intro heq
    have hterm : ∀ y ∈ (univ : Finset Ω),
        tiltWeight r p t y * (r y - a) ^ 2 ≤ tiltWeight r p t y * ((M - m) ^ 2 / 4) := by
      intro y _
      have h1 := hm y
      have h2 := hM y
      have hsq : (r y - a) ^ 2 ≤ (M - m) ^ 2 / 4 := by
        rw [ha]; nlinarith [sq_nonneg (r y - a)]
      exact mul_le_mul_of_nonneg_left hsq (hw y).le
    have hle : ∑ y, tiltWeight r p t y * (r y - a) ^ 2 ≤ (M - m) ^ 2 / 4 := by
      have := Finset.sum_le_sum hterm
      rwa [← Finset.sum_mul, hsum, one_mul] at this
    have hmid : tiltMean r p t = a := by
      have hsq : (tiltMean r p t - a) ^ 2 ≤ 0 := by
        rw [heq] at hkey; linarith
      have := sq_nonneg (tiltMean r p t - a)
      have hz : tiltMean r p t - a = 0 := by
        have : (tiltMean r p t - a) ^ 2 = 0 := le_antisymm hsq this
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      linarith
    have hSeq : ∑ y, tiltWeight r p t y * (r y - a) ^ 2
        = ∑ y, tiltWeight r p t y * ((M - m) ^ 2 / 4) := by
      rw [← Finset.sum_mul, hsum, one_mul]
      rw [heq, hmid] at hkey
      simpa using hkey.symm
    have hall := (Finset.sum_eq_sum_iff_of_le hterm).mp hSeq
    refine ⟨fun y => ?_, by rw [hmid, ha]⟩
    have hy := hall y (Finset.mem_univ y)
    have hcancel : (r y - a) ^ 2 = (M - m) ^ 2 / 4 :=
      mul_left_cancel₀ (ne_of_gt (hw y)) hy
    have hfac : (r y - M) * (r y - m) = 0 := by
      rw [ha] at hcancel; nlinarith [hcancel]
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro ⟨hvals, hmean⟩
    have hterm : ∀ y ∈ (univ : Finset Ω),
        tiltWeight r p t y * (r y - a) ^ 2 = tiltWeight r p t y * ((M - m) ^ 2 / 4) := by
      intro y _
      rcases hvals y with h | h <;> rw [h, ha] <;> ring
    have hS : ∑ y, tiltWeight r p t y * (r y - a) ^ 2 = (M - m) ^ 2 / 4 := by
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, hsum, one_mul]
    have hz : tiltMean r p t - a = 0 := by rw [hmean, ha]; ring
    rw [hkey, hS, hz]
    ring
