-- Prove2me | solution 1 for FisherRao.TwoPoint.sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:13:07.82502+00:00
-- url     : https://prove2.me/submissions/2d5c05ff-e630-4468-8ede-6592601764ab

-- Sol generated from Algebra/FisherRaoLength/Core.lean
import Mathlib
import Definitions.Def_Algebra_FisherRaoLength_Core
import Theorems.Thm_FisherRao_TwoPoint_fisherRaoLength_eq_arcsin
/-
# The `L¹` bound integrates to a Fisher–Rao length bound

This file proves the main theorem `l1_le_fisherRao_length`: along any smooth
curve of (strictly positive) probability vectors, the `L¹` distance between the
endpoints is bounded by the Fisher–Rao length of the curve.

The infinitesimal statement is a Cauchy–Schwarz inequality on the simplex,

  `∑ᵢ |vᵢ| = ∑ᵢ (|vᵢ| / √pᵢ) · √pᵢ ≤ √(∑ᵢ vᵢ²/pᵢ) · √(∑ᵢ pᵢ) = √(∑ᵢ vᵢ²/pᵢ)`,

i.e. the `L¹` speed of a curve of probability vectors never exceeds its
Fisher–Rao speed.  Integrating this pointwise bound with the fundamental theorem
of calculus turns it into the global length bound.

## Main definitions

* `l1Dist`            — the `L¹` distance `∑ᵢ |pᵢ - qᵢ|` (twice total variation)
* `fisherRaoSpeed`    — `√(∑ᵢ vᵢ² / pᵢ)`, the Fisher–Rao norm of a tangent vector
* `fisherRaoLength`   — the integral of the Fisher–Rao speed along a curve

## Main results

* `l1_speed_le_fisherRaoSpeed` — the infinitesimal (Cauchy–Schwarz) bound
* `l1_le_fisherRao_length`     — the integrated length bound (main theorem)
* `l1_le_fisherRao_length_uIcc`— localized version, hypotheses only on `[a,b]`
* `tv_le_half_fisherRao_length`— total variation form of the main theorem
* `fisherRaoSpeed_eq_two_mul_sqrtSpeed` — Fisher–Rao speed is twice the
  Euclidean speed of the square-root (sphere) embedding
* `TwoPoint.fisherRaoLength_eq_arcsin`, `TwoPoint.l1_lt_fisherRaoLength`,
  `TwoPoint.sharp` — an exactly solvable family showing the inequality is
  strict but that the constant `1` is optimal
* `fisherRao_sq_tensor`, `fisherRaoSpeed_tensor` — Pythagorean tensorization
* `abs_sub_event_le_half_fisherRao_length` — no event's probability moves by
  more than half the length
* `sqrt_chord_le_half_fisherRao_length` — the sharper spherical chord bound
* `one_sub_bhattacharyya_le_sq_fisherRao_length` — Hellinger/Bhattacharyya form
* `l1Dist_le_two_mul_sqrt_one_sub_bhattacharyya_sq`,
  `l1Dist_le_sum_arccos_bhattacharyya` — the smoothness-free discrete analogue
-/

open Finset BigOperators Real MeasureTheory intervalIntegral

open FisherRao

variable {ι : Type*} [Fintype ι]

/-! ## Definitions -/




/-! ## Elementary properties -/





/-! ## The infinitesimal bound: Cauchy–Schwarz on the simplex -/


/-! ## Continuity and integrability infrastructure -/


variable {p v : ℝ → ι → ℝ}





/-! ## The main theorem -/



/-! ## Structural properties of the length functional -/



/-! ## The square-root (sphere) embedding

The Fisher–Rao metric is, up to the factor `4`, the Euclidean metric pulled back
along `p ↦ √p`.  Concretely, if `pᵢ` moves with velocity `vᵢ`, then `√pᵢ` moves
with velocity `vᵢ / (2√pᵢ)`, and hence `∑ᵢ (d/dt √pᵢ)² = ¼ ∑ᵢ vᵢ²/pᵢ`. -/





/-! ## Sharpness: an explicit two-point family

To show that the constant `1` in `l1_le_fisherRao_length` cannot be improved we
compute both sides exactly for the curve

  `t ↦ ((1 + r·sin t)/2, (1 - r·sin t)/2)`,  `t ∈ [0, π/2]`,  `0 ≤ r < 1`,

in the interior of the 1-dimensional simplex.  Its `L¹` displacement is `r`
while its Fisher–Rao length is `arcsin r`; the ratio tends to `1` as `r → 0`,
and is `> 1` for every `r ∈ (0,1)` (so the inequality is always strict for
non-constant curves in this family). -/

open TwoPoint











/-- **Exact `L¹` displacement of the two-point family.** -/
theorem l1Dist_eq (r : ℝ) (hr0 : 0 ≤ r) :
    l1Dist (curve r (Real.pi / 2)) (curve r 0) = r := by
  simp only [l1Dist, curve, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    Real.sin_pi_div_two, Real.sin_zero, mul_one, mul_zero]
  rw [show (1 + r) / 2 - (1 + 0) / 2 = r / 2 by ring,
    show (1 - r) / 2 - (1 - 0) / 2 = -(r / 2) by ring, abs_neg,
    abs_of_nonneg (by linarith : (0:ℝ) ≤ r / 2)]
  ring





/-! ## Tensorization: the Fisher–Rao metric is Pythagorean under products

If two independent systems move simultaneously, the product distribution
`p ⊗ q` has velocity `v ⊗ q + p ⊗ w`, and its squared Fisher–Rao speed is the
sum of the squared speeds of the factors.  The cross term vanishes precisely
because a curve of probability vectors has velocity of total mass `0`. -/


variable {κ : Type*} [Fintype κ]





/-! ## Statistical consequence: distinguishability of events

The `L¹` bound controls how much the probability of *any* event can change
along a curve: total variation distance is half the `L¹` distance. -/





/-! ## A localized strengthening

The hypotheses of `l1_le_fisherRao_length` ask for a globally defined positive
probability curve.  In fact only the behaviour on `[a,b]` matters; this is the
version one applies to curves (such as straight segments in the simplex) that
leave the simplex outside the interval of interest. -/


/-! ## Hellinger bridge

The squared Hellinger distance `H²(p,q) = ½‖√p − √q‖²` is dominated by the
total variation distance, hence by half the Fisher–Rao length.  This links the
`L¹` length bound to the square-root (sphere) picture of Fisher–Rao geometry. -/




/-! ## The sharper spherical chord bound

The `L¹` bound is one shadow of a stronger geometric fact: the *chord* of the
square-root embedding is at most half the Fisher–Rao length.  The proof is the
same Cauchy–Schwarz/FTC mechanism, but applied to the single scalar function
`t ↦ ⟨Δ, √p t⟩ / ‖Δ‖` where `Δ = √p b − √p a`; this device replaces
vector-valued integration by an ordinary one-dimensional integral.

Note that no simplex constraint is needed here: the statement is purely
metric. -/






/-! ## The discrete (Markov-path) length bound

Dropping smoothness entirely, one can still bound the `L¹` displacement of a
finite path of distributions by a sum of *Bhattacharyya angles*
`arccos BC(pᵏ, pᵏ⁺¹)`, which is the natural discrete Fisher–Rao length:
`arccos BC` is precisely the spherical distance between the square-root
embeddings.  The single-step inequality is Le Cam's `‖p−q‖₁ ≤ 2√(1 − BC²)`,
proved by the same Cauchy–Schwarz mechanism as the infinitesimal bound. -/









open FisherRao.TwoPoint in
theorem solution(ε : ℝ) (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      fisherRaoLength (curve r) (vel r) 0 (Real.pi / 2)
        ≤ (1 + ε) * l1Dist (curve r (Real.pi / 2)) (curve r 0) := by
  set d : ℝ := min 1 (Real.sqrt ε) with hd
  have hd1 : d ≤ 1 := min_le_left _ _
  have hdpos : 0 < d := lt_min one_pos (Real.sqrt_pos.mpr hε)
  have hdsq : d ^ 2 ≤ ε := by
    rcases le_total (Real.sqrt ε) 1 with h | h
    · have : d = Real.sqrt ε := by rw [hd, min_eq_right h]
      rw [this, Real.sq_sqrt hε.le]
    · have : d = 1 := by rw [hd, min_eq_left h]
      have : (1:ℝ) ≤ ε := by
        nlinarith [Real.sq_sqrt hε.le, Real.sqrt_nonneg ε]
      simpa [‹d = 1›] using this
  refine ⟨Real.sin d, Real.sin_pos_of_pos_of_lt_pi hdpos (by linarith [Real.pi_gt_three]), ?_, ?_⟩
  · calc Real.sin d < d := Real.sin_lt hdpos
      _ ≤ 1 := hd1
  · have hsin_pos : 0 < Real.sin d :=
      Real.sin_pos_of_pos_of_lt_pi hdpos (by linarith [Real.pi_gt_three])
    have hsin_lt1 : Real.sin d < 1 := lt_of_lt_of_le (Real.sin_lt hdpos) hd1
    rw [l1Dist_eq _ hsin_pos.le, fisherRaoLength_eq_arcsin _ hsin_pos.le hsin_lt1,
      Real.arcsin_sin (by linarith [Real.pi_gt_three]) (by linarith [Real.pi_gt_three])]
    have hcube : d - d ^ 3 / 4 < Real.sin d := Real.sin_gt_sub_cube hdpos hd1
    have hd2 : d ^ 2 ≤ 1 := by nlinarith
    have key : (1 + ε) * d ^ 2 / 4 ≤ ε := by nlinarith
    have step1 : d ≤ (1 + ε) * (d - d ^ 3 / 4) := by
      nlinarith [mul_nonneg hdpos.le (sub_nonneg.mpr key)]
    have step2 : (1 + ε) * (d - d ^ 3 / 4) ≤ (1 + ε) * Real.sin d := by nlinarith
    linarith
