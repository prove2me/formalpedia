-- Prove2me | Theorems.Thm_FisherRao_l1Dist_le_sum_arccos_bhattacharyya
-- name    : FisherRao.l1Dist_le_sum_arccos_bhattacharyya
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T10:33:03.207248+00:00
-- url     : https://prove2.me/theorems/f3f4fcb1-2796-4b24-b7a7-938a701d19f4
-- title:
--   Discrete Fisher–Rao length bound.
-- statement:
--   **Discrete Fisher–Rao length bound.**  For any finite path of probability
--   vectors, the `L¹` displacement between the endpoints is at most the sum of the
--   Bhattacharyya angles of the consecutive steps — the discrete counterpart of
--   `l1_le_fisherRao_length`, requiring no smoothness at all.
--
--   ```lean
--   theorem FisherRao.l1Dist_le_sum_arccos_bhattacharyya(P : ℕ → ι → ℝ)
--       (hp : ∀ k i, 0 ≤ P k i) (hp1 : ∀ k, ∑ i, P k i = 1) (N : ℕ) :
--       l1Dist (P N) (P 0) ≤ ∑ k ∈ Finset.range N, 2 * Real.arccos (bhattacharyya (P k) (P (k + 1))) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/FisherRaoLength/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/FisherRaoLength/Core.lean#L786

-- Thm stub generated from Algebra/FisherRaoLength/Core.lean
import Mathlib
import Definitions.Def_Algebra_FisherRaoLength_Core
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

theorem FisherRao.l1Dist_le_sum_arccos_bhattacharyya(P : ℕ → ι → ℝ)
    (hp : ∀ k i, 0 ≤ P k i) (hp1 : ∀ k, ∑ i, P k i = 1) (N : ℕ) :
    l1Dist (P N) (P 0) ≤ ∑ k ∈ Finset.range N, 2 * Real.arccos (bhattacharyya (P k) (P (k + 1))) := by sorry
