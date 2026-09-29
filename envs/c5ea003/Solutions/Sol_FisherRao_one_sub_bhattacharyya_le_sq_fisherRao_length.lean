-- Prove2me | solution 1 for FisherRao.one_sub_bhattacharyya_le_sq_fisherRao_length
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:25:12.715823+00:00
-- url     : https://prove2.me/submissions/658b02bd-bf08-4426-978f-bac03949cfcd

-- Sol generated from Algebra/FisherRaoLength/Core.lean
import Mathlib
import Definitions.Def_Algebra_FisherRaoLength_Core
import Theorems.Thm_FisherRao_sqrt_chord_le_half_fisherRao_length
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




theorem fisherRaoSpeed_nonneg (p v : ι → ℝ) : 0 ≤ fisherRaoSpeed p v := Real.sqrt_nonneg _

/-! ## The infinitesimal bound: Cauchy–Schwarz on the simplex -/


/-! ## Continuity and integrability infrastructure -/


variable {p v : ℝ → ι → ℝ}





/-! ## The main theorem -/



/-! ## Structural properties of the length functional -/

theorem fisherRaoLength_nonneg (p v : ℝ → ι → ℝ) {a b : ℝ} (hab : a ≤ b) :
    0 ≤ fisherRaoLength p v a b :=
  intervalIntegral.integral_nonneg hab fun t _ => fisherRaoSpeed_nonneg (p t) (v t)


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









open FisherRao in
theorem solution{p v : ℝ → ι → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hderiv : ∀ t i, HasDerivAt (fun s => p s i) (v t i) t)
    (hv : ∀ i, Continuous fun t => v t i)
    (hpos : ∀ t i, 0 < p t i) (hp1 : ∀ t, ∑ i, p t i = 1) :
    1 - ∑ i, Real.sqrt (p b i * p a i) ≤ (1 / 8) * (fisherRaoLength p v a b) ^ 2 := by
  have hchord := sqrt_chord_le_half_fisherRao_length hab hderiv hv hpos
  have hnn : 0 ≤ ∑ i, (Real.sqrt (p b i) - Real.sqrt (p a i)) ^ 2 :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hsq : (Real.sqrt (∑ i, (Real.sqrt (p b i) - Real.sqrt (p a i)) ^ 2)) ^ 2
      = ∑ i, (Real.sqrt (p b i) - Real.sqrt (p a i)) ^ 2 := Real.sq_sqrt hnn
  have hexpand : ∑ i, (Real.sqrt (p b i) - Real.sqrt (p a i)) ^ 2
      = 2 - 2 * ∑ i, Real.sqrt (p b i * p a i) := by
    have hterm : ∀ i : ι, (Real.sqrt (p b i) - Real.sqrt (p a i)) ^ 2
        = p b i + p a i - 2 * Real.sqrt (p b i * p a i) := by
      intro i
      rw [Real.sqrt_mul (hpos b i).le]
      have h1 : Real.sqrt (p b i) ^ 2 = p b i := Real.sq_sqrt (hpos b i).le
      have h2 : Real.sqrt (p a i) ^ 2 = p a i := Real.sq_sqrt (hpos a i).le
      nlinarith [h1, h2]
    rw [Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, hp1 a, hp1 b, ← Finset.mul_sum]
    norm_num
  have hlen : 0 ≤ fisherRaoLength p v a b := fisherRaoLength_nonneg p v hab
  have hchordnn : 0 ≤ Real.sqrt (∑ i, (Real.sqrt (p b i) - Real.sqrt (p a i)) ^ 2) :=
    Real.sqrt_nonneg _
  nlinarith [hchord, hsq, hexpand, hchordnn, hlen]
