-- Prove2me | Theorems.Thm_sum_norm_sq_rank_one_outer_product_loewner_le_scalar_mul_sum
-- name    : sum_norm_sq_rank_one_outer_product_loewner_le_scalar_mul_sum
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-24T01:32:24.86243+00:00
-- url     : https://prove2.me/theorems/d24a0b1f-9b50-4337-8cad-0040f1c5a392
-- statement:
--   **PSD-monotone Loewner domination step.** For a finite family of rank-one outer products `y_c (x) y_c = vecMulVec y_c y_c` and a scalar `M` dominating every squared norm `||y_c||^2 = y_c . y_c`, the weighted Gram sum is dominated in the Loewner order: `sum_c ||y_c||^2 (y_c (x) y_c) ⪯ M . sum_c (y_c (x) y_c)`, stated as the difference `M . sum (y_c(x)y_c) - sum ||y_c||^2 (y_c(x)y_c)` being positive semidefinite. This is the PSD-monotone domination immediately after the Gram-square collapse `sum_c (y_c(x)y_c)^2 = sum_c ||y_c||^2 (y_c(x)y_c)` in Rudelson's noncommutative-Khintchine selection lemma. Proof: the difference equals `sum_c (M - ||y_c||^2) (y_c (x) y_c)`; each `y_c (x) y_c` is PSD, each scalar `M - ||y_c||^2 >= 0`, a nonnegative scalar multiple of a PSD matrix is PSD, and a finite sum of PSD matrices is PSD.
-- source:
--   Standard PSD / Loewner-order monotonicity. The rank-one outer products y_c (x) y_c = vecMulVec y_c y_c are positive semidefinite; for a scalar bound M >= ||y_c||^2 = y_c . y_c, each (M - ||y_c||^2)(y_c (x) y_c) is PSD (nonnegative scalar times PSD), and a finite sum of PSD matrices is PSD. This is the PSD-monotone domination step of Rudelson's noncommutative-Khintchine selection lemma (Rudelson, J. Funct. Anal. 164 (1999), Thm 1; van Handel, 'Structured Random Matrices', arXiv:1610.05200 Sec. 3; Candes-Recht 2009 arXiv:0805.4471 Sec. 4.2): sum_c ||y_c||^2 (y_c (x) y_c) <= max_c ||y_c||^2 . sum_c (y_c (x) y_c) in the Loewner order, i.e. the difference M . sum (y_c(x)y_c) - sum ||y_c||^2 (y_c(x)y_c) is positive semidefinite.

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.StarOrdered
open scoped BigOperators Matrix

theorem sum_norm_sq_rank_one_outer_product_loewner_le_scalar_mul_sum {d : Nat} {ι : Type*} (s : Finset ι) (y : ι → Fin d → Real) (M : Real) (hM : ∀ c ∈ s, (y c ⬝ᵥ y c) ≤ M) : (M • (∑ c ∈ s, Matrix.vecMulVec (y c) (y c)) - ∑ c ∈ s, (y c ⬝ᵥ y c) • Matrix.vecMulVec (y c) (y c)).PosSemidef := by sorry
