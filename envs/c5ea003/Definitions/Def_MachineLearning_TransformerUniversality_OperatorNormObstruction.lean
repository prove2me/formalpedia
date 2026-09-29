-- Prove2me | Definitions.Def_MachineLearning_TransformerUniversality_OperatorNormObstruction
-- name    : MachineLearning_TransformerUniversality_OperatorNormObstruction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:16:43.841144+00:00
-- url     : https://prove2.me/theorems/0d2f9de0-1490-4274-8b9c-1627894140c8
-- title:
--   Aether Catalog definitions — MachineLearning_TransformerUniversality_OperatorNormObstruction
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TransformerUniversality.OperatorNormObstruction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TransformerUniversality/OperatorNormObstruction.lean by skeleton subtraction
import Mathlib

/-!
# The spectral form of the low-rank obstruction: head width is a dimension-free resource

`Catalog/MachineLearning/TransformerUniversality/LowRankQuantitative.lean` proves that the
score matrix of a head of width `dk < d` has some *entry* at distance at least `β / d` from the
exact-selection pattern `β • 1`, and that the constant `1/d` is optimal for the entrywise
(sup-norm) distance.  The third next-cycle sub-conjecture of `FUTURE_DIRECTIONS.md` asked
whether that bound upgrades to the operator norm "with the same constant `β / d`".

This file settles it, and the answer is **stronger than conjectured**: in the operator norm the
obstruction is `β`, with *no* dimension factor at all, and this is again exactly optimal.  The
`1/d` of the entrywise statement was therefore an artifact of measuring a rank-one deviation in
the sup norm — spreading an error of spectral size `β` over `d²` entries makes each entry small,
but the error itself never shrinks.

Main results:

* `beta_le_of_opNormLe` — **lower bound**: if `S` is singular and every vector satisfies
  `‖(S − β•1)v‖ ≤ r‖v‖` (with `r ≥ 0`), then `β ≤ r`.  The proof takes a kernel vector `v`,
  on which the deviation acts as `−β·v` exactly, so the deviation has an eigenvalue of modulus
  `β`.
* `centeringScaled_opNormLe` — **matching construction**: the scaled centering matrix
  `β(1 − J/d)` is singular and satisfies `‖(β(1 − J/d) − β•1)v‖ ≤ β‖v‖`, by Cauchy–Schwarz.
* `spectral_distance_to_scaled_identity` — hence `IsLeast`: the spectral distance from `β • 1`
  to the singular matrices is **exactly `β`**.
* `qk_spectral_far_from_scaled_identity`, `headDim_lower_bound_of_spectral_approx` — the
  architectural corollaries: a head of width `dk < d` is at spectral distance at least `β` from
  the exact-selection pattern, uniformly in `d`, so a *relative* spectral accuracy better than
  `100 %` already forces full head width.

The contrast with `LowRankQuantitative.entrywise_distance_to_identity_eq` (`1/d`) is the point:
the two norms give genuinely different resource statements, and the operator-norm one is the
one that survives taking `d → ∞`.
-/

open scoped BigOperators
open Matrix

namespace OperatorNormObstruction

variable {n : ℕ}

/-! ## Squared Euclidean norm and the operator-norm predicate -/

/-- The squared Euclidean norm of a coordinate vector.  Using the *squared* norm keeps every
statement polynomial and avoids `Real.sqrt`. -/
def sqNorm (v : Fin n → ℝ) : ℝ := ∑ i, (v i) ^ 2



/-- `OpNormLe M r` says that the matrix `M` has operator norm at most `r`, expressed with
squared Euclidean norms. -/
def OpNormLe (M : Matrix (Fin n) (Fin n) ℝ) (r : ℝ) : Prop :=
  ∀ v : Fin n → ℝ, sqNorm (M.mulVec v) ≤ r ^ 2 * sqNorm v

/-! ## Singularity from a kernel vector -/



/-! ## The spectral lower bound -/




/-! ## Sharpness: the scaled centering matrix -/

/-- The scaled centering matrix `β(1 − J/n)`. -/
noncomputable def centeringScaled (n : ℕ) (beta : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => beta * ((if i = j then (1 : ℝ) else 0) - (n : ℝ)⁻¹)





/-! ## Architectural corollaries for narrow attention heads -/

section Heads

variable {d dk : ℕ}

/-- The learned score matrix of a head of width `dk` (cf. `LowRankQuantitative.scoreMatrix`). -/
def scoreMatrix (WQ WK : Matrix (Fin dk) (Fin d) ℝ) : Matrix (Fin d) (Fin d) ℝ := WQᵀ * WK




end Heads

end OperatorNormObstruction


