-- Prove2me | Definitions.Def_Algebra_FisherRaoLength_Core
-- name    : Algebra_FisherRaoLength_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:14:27.15005+00:00
-- url     : https://prove2.me/theorems/523dfdc1-469f-4f5d-88c5-6d44ff32f2ca
-- title:
--   Aether Catalog definitions — Algebra_FisherRaoLength_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.FisherRaoLength.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/FisherRaoLength/Core.lean by skeleton subtraction
import Mathlib
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

namespace FisherRao

variable {ι : Type*} [Fintype ι]

/-! ## Definitions -/

/-- The `L¹` (total-variation-type) distance between two finite vectors. -/
noncomputable def l1Dist (p q : ι → ℝ) : ℝ := ∑ i, |p i - q i|

/-- The Fisher–Rao (information-metric) norm of a tangent vector `v` at the
point `p` of the open simplex: `√(∑ᵢ vᵢ² / pᵢ)`. -/
noncomputable def fisherRaoSpeed (p v : ι → ℝ) : ℝ := Real.sqrt (∑ i, (v i) ^ 2 / p i)

/-- The Fisher–Rao length of the curve `t ↦ p t` with velocity field `t ↦ v t`,
computed over the interval `[a, b]`. -/
noncomputable def fisherRaoLength (p v : ℝ → ι → ℝ) (a b : ℝ) : ℝ :=
  ∫ t in a..b, fisherRaoSpeed (p t) (v t)

/-! ## Elementary properties -/





/-! ## The infinitesimal bound: Cauchy–Schwarz on the simplex -/


/-! ## Continuity and integrability infrastructure -/

section Curve

variable {p v : ℝ → ι → ℝ}




end Curve

/-! ## The main theorem -/



/-! ## Structural properties of the length functional -/



/-! ## The square-root (sphere) embedding

The Fisher–Rao metric is, up to the factor `4`, the Euclidean metric pulled back
along `p ↦ √p`.  Concretely, if `pᵢ` moves with velocity `vᵢ`, then `√pᵢ` moves
with velocity `vᵢ / (2√pᵢ)`, and hence `∑ᵢ (d/dt √pᵢ)² = ¼ ∑ᵢ vᵢ²/pᵢ`. -/

/-- The velocity of the square-root embedding. -/
noncomputable def sqrtVelocity (p v : ι → ℝ) : ι → ℝ := fun i => v i / (2 * Real.sqrt (p i))




/-! ## Sharpness: an explicit two-point family

To show that the constant `1` in `l1_le_fisherRao_length` cannot be improved we
compute both sides exactly for the curve

  `t ↦ ((1 + r·sin t)/2, (1 - r·sin t)/2)`,  `t ∈ [0, π/2]`,  `0 ≤ r < 1`,

in the interior of the 1-dimensional simplex.  Its `L¹` displacement is `r`
while its Fisher–Rao length is `arcsin r`; the ratio tends to `1` as `r → 0`,
and is `> 1` for every `r ∈ (0,1)` (so the inequality is always strict for
non-constant curves in this family). -/

namespace TwoPoint

/-- The two-point curve `t ↦ ((1 + r sin t)/2, (1 - r sin t)/2)`. -/
noncomputable def curve (r : ℝ) : ℝ → Fin 2 → ℝ :=
  fun t => ![(1 + r * Real.sin t) / 2, (1 - r * Real.sin t) / 2]

/-- Its velocity field. -/
noncomputable def vel (r : ℝ) : ℝ → Fin 2 → ℝ :=
  fun t => ![r * Real.cos t / 2, -(r * Real.cos t) / 2]













end TwoPoint

/-! ## Tensorization: the Fisher–Rao metric is Pythagorean under products

If two independent systems move simultaneously, the product distribution
`p ⊗ q` has velocity `v ⊗ q + p ⊗ w`, and its squared Fisher–Rao speed is the
sum of the squared speeds of the factors.  The cross term vanishes precisely
because a curve of probability vectors has velocity of total mass `0`. -/

section Tensor

variable {κ : Type*} [Fintype κ]




end Tensor

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

/-- Velocity of the square-root embedding along the curve. -/
noncomputable def sqrtVel (p v : ℝ → ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  v t i / (2 * Real.sqrt (p t i))





/-! ## The discrete (Markov-path) length bound

Dropping smoothness entirely, one can still bound the `L¹` displacement of a
finite path of distributions by a sum of *Bhattacharyya angles*
`arccos BC(pᵏ, pᵏ⁺¹)`, which is the natural discrete Fisher–Rao length:
`arccos BC` is precisely the spherical distance between the square-root
embeddings.  The single-step inequality is Le Cam's `‖p−q‖₁ ≤ 2√(1 − BC²)`,
proved by the same Cauchy–Schwarz mechanism as the infinitesimal bound. -/

/-- The Bhattacharyya coefficient `∑ᵢ √(pᵢ qᵢ)`; it is the inner product of the
square-root embeddings, i.e. the cosine of the spherical angle between them. -/
noncomputable def bhattacharyya (p q : ι → ℝ) : ℝ := ∑ i, Real.sqrt (p i * q i)







end FisherRao


