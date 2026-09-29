-- Prove2me | solution 1 for OperatorNormObstruction.centeringScaled_opNormLe
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:26:16.248772+00:00
-- url     : https://prove2.me/submissions/ecda181d-d172-4b50-8586-ea71183eb822

-- Sol generated from MachineLearning/TransformerUniversality/OperatorNormObstruction.lean
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



/-- The deviation of the scaled centering matrix from `β•1` is the rank-one matrix `−(β/n)J`. -/
theorem centeringScaled_deviation (beta : ℝ) (i j : Fin n) :
    (centeringScaled n beta - beta • (1 : Matrix (Fin n) (Fin n) ℝ)) i j = -(beta / n) := by
  simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, centeringScaled,
    Matrix.of_apply, smul_eq_mul]
  by_cases h : i = j <;> simp [h] <;> ring



/-! ## Architectural corollaries for narrow attention heads -/


variable {d dk : ℕ}







open OperatorNormObstruction in
theorem solution(hn : 0 < n) (beta : ℝ) :
    OpNormLe (centeringScaled n beta - beta • (1 : Matrix (Fin n) (Fin n) ℝ)) beta := by
  intro v
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmul : ∀ i, (centeringScaled n beta -
      beta • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec v i = -(beta / n) * ∑ j, v j := by
    intro i
    simp only [Matrix.mulVec, dotProduct, centeringScaled_deviation, Finset.mul_sum]
  have hsq : sqNorm ((centeringScaled n beta -
      beta • (1 : Matrix (Fin n) (Fin n) ℝ)).mulVec v)
      = n * ((beta / n) ^ 2 * (∑ j, v j) ^ 2) := by
    simp only [sqNorm, hmul]
    rw [Finset.sum_congr rfl (fun i _ => by ring :
      ∀ i ∈ (Finset.univ : Finset (Fin n)), (-(beta / n) * ∑ j, v j) ^ 2
        = (beta / n) ^ 2 * (∑ j, v j) ^ 2)]
    simp [Finset.sum_const, nsmul_eq_mul]
  have hcs : (∑ j, v j) ^ 2 ≤ n * sqNorm v := by
    have h := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n))) (f := v)
    simpa [sqNorm] using h
  rw [hsq]
  have hb2 : (0 : ℝ) ≤ beta ^ 2 := sq_nonneg beta
  have key : n * ((beta / n) ^ 2 * (∑ j, v j) ^ 2) = (beta ^ 2 / n) * (∑ j, v j) ^ 2 := by
    field_simp
  rw [key]
  have hstep : (beta ^ 2 / n) * (∑ j, v j) ^ 2 ≤ (beta ^ 2 / n) * (n * sqNorm v) :=
    mul_le_mul_of_nonneg_left hcs (by positivity)
  calc (beta ^ 2 / n) * (∑ j, v j) ^ 2 ≤ (beta ^ 2 / n) * (n * sqNorm v) := hstep
    _ = beta ^ 2 * sqNorm v := by field_simp
