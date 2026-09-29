-- Prove2me | Theorems.Thm_rudelson_selection_gram_spectral_bound
-- name    : rudelson_selection_gram_spectral_bound
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-24T17:17:05.982995+00:00
-- url     : https://prove2.me/theorems/ecb2e14b-d3f1-4bb9-b52e-1f75e00ebf84
-- statement:
--   **Rudelson selection one-sided Gram spectral bound (rank-one form).** For a finite family of vectors $y : \iota \to \mathbb{R}^d$ with $\|y_c\|^2 = y_c \cdot y_c \le M$ for all $c \in s$ (and $0 \le M$), the spectral norm of the energy-weighted Gram operator is dominated by $M$ times the spectral norm of the plain Gram operator: $$\Big\| \sum_{c} \|y_c\|^2\, (y_c \otimes y_c) \Big\| \le M \, \Big\| \sum_{c} (y_c \otimes y_c) \Big\|.$$ Here $y_c \otimes y_c = $ `Matrix.vecMulVec (y c) (y c)` is the rank-one outer product and the norm is the $\ell^2$ operator norm `‖Matrix.toEuclideanCLM (𝕜 := ℝ) X‖`. This is the spectral consequence of the rank-one squaring identity $(yy^*)^2 = \|y\|^2 (yy^*)$ combined with Loewner monotonicity, exactly the bound the noncommutative-Khintchine (Lust-Picquard) step of Rudelson's selection lemma applies to the one-sided Gram operator $\sum_c X_c^2$ with $X_c = y_c \otimes y_c$ self-adjoint. Proof (reduction): $\sum_c \|y_c\|^2 (y_c\otimes y_c) \preceq M \sum_c (y_c\otimes y_c)$ in the Loewner order (each summand is a nonnegative-scalar multiple of a PSD rank-one), then apply spectral-norm Loewner monotonicity and pull the scalar $M \ge 0$ out of the operator norm.
-- source:
--   Rudelson, 'Random vectors in the isotropic position', J. Funct. Anal. 164 (1999), Thm 1, Step 2; van Handel, 'Structured Random Matrices', arXiv:1610.05200 Sec. 3; Candes-Recht 2009 (arXiv:0805.4471) Sec. 6.1 / Thm 4.2 eq (4.9) p.18. Spectral (operator) norm here is the l2->l2 operator norm of the matrix as a map on Euclidean space, ||toEuclideanCLM X||, which for a square real matrix equals the platform spectralNorm.

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
open scoped Matrix BigOperators

theorem rudelson_selection_gram_spectral_bound {d : ℕ} {ι : Type*} (s : Finset ι) (y : ι → Fin d → ℝ) (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ c ∈ s, (y c ⬝ᵥ y c) ≤ M) : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ c ∈ s, (y c ⬝ᵥ y c) • Matrix.vecMulVec (y c) (y c))‖ ≤ M * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ c ∈ s, Matrix.vecMulVec (y c) (y c))‖ := by sorry
