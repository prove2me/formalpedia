-- Prove2me | Theorems.Thm_OperatorNormObstruction_centeringScaled_rank_lt
-- name    : OperatorNormObstruction.centeringScaled_rank_lt
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:44:49.662767+00:00
-- url     : https://prove2.me/theorems/783804a1-a536-484b-a4e0-4c57a6bc0754
-- title:
--   The scaled centering matrix kills the all-ones vector, hence is singular.
-- statement:
--   The scaled centering matrix kills the all-ones vector, hence is singular.
--
--   ```lean
--   theorem OperatorNormObstruction.centeringScaled_rank_lt(hn : 0 < n) (beta : ℝ) : (centeringScaled n beta).rank < n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TransformerUniversality/OperatorNormObstruction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransformerUniversality/OperatorNormObstruction.lean#L125

-- Thm stub generated from MachineLearning/TransformerUniversality/OperatorNormObstruction.lean
import Mathlib
import Definitions.Def_MachineLearning_TransformerUniversality_OperatorNormObstruction

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

open OperatorNormObstruction

variable {n : ℕ}

/-! ## Squared Euclidean norm and the operator-norm predicate -/





/-! ## Singularity from a kernel vector -/



/-! ## The spectral lower bound -/




/-! ## Sharpness: the scaled centering matrix -/

theorem OperatorNormObstruction.centeringScaled_rank_lt(hn : 0 < n) (beta : ℝ) : (centeringScaled n beta).rank < n := by sorry
