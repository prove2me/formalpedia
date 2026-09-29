-- Prove2me | solution 1 for FisherRao.TwoPoint.fisherRaoLength_eq_arcsin
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:08:57.903735+00:00
-- url     : https://prove2.me/submissions/41863035-1ad3-4e41-9c1a-a5edfb4ab9d7

-- Sol generated from Algebra/FisherRaoLength/Core.lean
import Mathlib
import Definitions.Def_Algebra_FisherRaoLength_Core
import Theorems.Thm_FisherRao_TwoPoint_speed_eq
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






theorem abs_r_sin_lt (r t : ℝ) (hr : |r| < 1) : |r * Real.sin t| < 1 := by
  have h1 : |r * Real.sin t| = |r| * |Real.sin t| := abs_mul _ _
  have h2 : |Real.sin t| ≤ 1 := Real.abs_sin_le_one t
  nlinarith [abs_nonneg r, abs_nonneg (Real.sin t)]



/-- The `arcsin` antiderivative of the Fisher–Rao speed. -/
theorem hasDerivAt_arcsin_comp (r : ℝ) (hr : |r| < 1) (t : ℝ) :
    HasDerivAt (fun s => Real.arcsin (r * Real.sin s))
      (r * Real.cos t / Real.sqrt (1 - (r * Real.sin t) ^ 2)) t := by
  have hu1 : |r * Real.sin t| < 1 := abs_r_sin_lt r t hr
  rw [abs_lt] at hu1
  have hin : HasDerivAt (fun s : ℝ => r * Real.sin s) (r * Real.cos t) t :=
    (Real.hasDerivAt_sin t).const_mul r
  have hout : HasDerivAt Real.arcsin (1 / Real.sqrt (1 - (r * Real.sin t) ^ 2))
      (r * Real.sin t) :=
    Real.hasDerivAt_arcsin (by linarith [hu1.1]) (by linarith [hu1.2])
  have := hout.comp t hin
  simpa [Function.comp, div_eq_mul_inv, mul_comm, mul_assoc, mul_left_comm] using this







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
theorem solution(r : ℝ) (hr0 : 0 ≤ r) (hr : r < 1) :
    fisherRaoLength (curve r) (vel r) 0 (Real.pi / 2) = Real.arcsin r := by
  have hrabs : |r| < 1 := by rw [abs_lt]; constructor <;> linarith
  have hcont : Continuous fun t : ℝ => r * Real.cos t / Real.sqrt (1 - (r * Real.sin t) ^ 2) := by
    have hden : ∀ t : ℝ, Real.sqrt (1 - (r * Real.sin t) ^ 2) ≠ 0 := by
      intro t
      have hu1 : |r * Real.sin t| < 1 := abs_r_sin_lt r t hrabs
      have : (r * Real.sin t) ^ 2 < 1 := (sq_lt_one_iff_abs_lt_one _).mpr hu1
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith))
    exact (continuous_const.mul Real.continuous_cos).div
      ((continuous_const.sub ((continuous_const.mul Real.continuous_sin).pow 2)).sqrt) hden
  have hEq : fisherRaoLength (curve r) (vel r) 0 (Real.pi / 2)
      = ∫ t in (0:ℝ)..(Real.pi / 2), r * Real.cos t / Real.sqrt (1 - (r * Real.sin t) ^ 2) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le (by positivity)] at ht
    have hcos : 0 ≤ Real.cos t :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [ht.1, Real.pi_pos], ht.2⟩
    exact speed_eq r hrabs t (by positivity)
  rw [hEq, intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_arcsin_comp r hrabs t) (hcont.intervalIntegrable _ _)]
  simp
