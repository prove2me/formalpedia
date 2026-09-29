-- Prove2me | solution 1 for BKModule.example_not_finiteHeight
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T11:57:48.004307+00:00
-- url     : https://prove2.me/submissions/75aa3854-ccd4-4714-9881-5496ec062dbe

import Mathlib
import Definitions.Def_Novelty_FiniteHeightConverse
open Polynomial Matrix in
theorem solution :
    ¬ (⟨1, !![(X : ℚ[X]) + 1]⟩ : BKModule ℚ[X]).FiniteHeight X := by
  rintro ⟨h, B, hB, -⟩
  -- the `(0,0)` entry: `(X + 1) · B₀₀ = X ^ h`
  have h00 := congrFun (congrFun hB 0) 0
  simp only [Matrix.mul_apply, Fin.sum_univ_one, Matrix.smul_apply, Matrix.one_apply_eq,
    smul_eq_mul, mul_one, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.empty_val', Matrix.cons_val_fin_one] at h00
  -- evaluate at `-1`: the left side vanishes, the right side is `(-1)^h ≠ 0`
  have := congrArg (Polynomial.eval (-1 : ℚ)) h00
  simp only [eval_mul, eval_add, eval_X, eval_one, eval_pow, neg_add_cancel, zero_mul] at this
  exact pow_ne_zero h (by norm_num : (-1 : ℚ) ≠ 0) this.symm
