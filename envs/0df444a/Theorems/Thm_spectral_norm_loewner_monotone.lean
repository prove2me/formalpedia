-- Prove2me | Theorems.Thm_spectral_norm_loewner_monotone
-- name    : spectral_norm_loewner_monotone
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-06-24T17:16:57.107943+00:00
-- url     : https://prove2.me/theorems/aebc678c-8776-4f9c-b654-a02e97bc6c47
-- statement:
--   **Spectral-norm Loewner monotonicity.** For real symmetric matrices $A, B$ with $A \preceq B$ in the Loewner order (i.e. $A$ positive semidefinite and $B - A$ positive semidefinite), the spectral (operator) norms are ordered: $\|A\| \le \|B\|$. Here the spectral norm is the $\ell^2 \to \ell^2$ operator norm of the matrix acting on Euclidean space, written `‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖`. This is the operator-theoretic bridge that converts a rank-one Loewner domination into a one-sided spectral bound, used by the noncommutative-Khintchine / Lust-Picquard step of Rudelson's selection lemma. Proof: both operators are self-adjoint (the matrices are Hermitian); the norm of a symmetric operator equals $\sup_x |\langle Tx, x\rangle| / \|x\|^2$ (the Rayleigh quotient); PSD of $A$ makes its Rayleigh quotient nonnegative, and PSD of $B-A$ gives $x^\top A x \le x^\top B x$ pointwise, so the supremum is dominated by $\|B\|$.
-- source:
--   Rudelson, 'Random vectors in the isotropic position', J. Funct. Anal. 164 (1999), Thm 1, Step 2; van Handel, 'Structured Random Matrices', arXiv:1610.05200 Sec. 3; Candes-Recht 2009 (arXiv:0805.4471) Sec. 6.1 / Thm 4.2 eq (4.9) p.18. Spectral (operator) norm here is the l2->l2 operator norm of the matrix as a map on Euclidean space, ||toEuclideanCLM X||, which for a square real matrix equals the platform spectralNorm.

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
open scoped Matrix BigOperators

theorem spectral_norm_loewner_monotone {n : Nat} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) (hBA : (B - A).PosSemidef) : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖ := by sorry
