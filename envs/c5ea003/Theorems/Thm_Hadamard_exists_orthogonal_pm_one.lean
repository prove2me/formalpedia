-- Prove2me | Theorems.Thm_Hadamard_exists_orthogonal_pm_one
-- name    : Hadamard.exists_orthogonal_pm_one
-- status  : Open
-- author  : @carlok
-- created : 2026-09-07T01:06:47.668718+00:00
-- url     : https://prove2.me/theorems/e4944c69-30f1-4637-a3c4-67b84958a6cb
-- title:
--   Hadamard's conjecture for odd multipliers, orthogonality form: $MM^{\mathsf T}=4kI$
-- statement:
--   **The Hadamard conjecture for odd multipliers, in orthogonality form.**
--
--   For every odd $k$ there is a matrix $M$ of order $4k$ with entries $\pm1$ satisfying
--   $$M M^{\mathsf T} = 4k\,I .$$
--
--   This is `Hadamard.odd_multiplier_exists` restated. The two forms are equivalent, but they are not equally usable: the determinant formulation measures a Hadamard matrix, while the orthogonality formulation *is* the combinatorial object. Every construction in the literature — Sylvester doubling, Paley's quadratic-residue families, Williamson's four-matrix method, Baumert–Hall arrays — produces and verifies $MM^{\mathsf T}=nI$ directly, row by row, and never touches a determinant. A formalization that has to re-derive orthogonality from a determinant identity each time is fighting its own statement.
--
--   **Why the implication holds.** If $MM^{\mathsf T}=nI$ then taking determinants gives $(\det M)^2=\det(nI)=n^{n}$, so $|\det M| = n^{n/2}$, which is exactly the extremal value in Hadamard's inequality. The companion reduction proves this direction, so this lemma implies the determinant form.
--
--   **What remains open.** Orders divisible by $4$ are the only candidates beyond $1$ and $2$: a $\pm1$ matrix with orthogonal rows and order $n>2$ forces $4\mid n$. Writing $n=4k$ and splitting on the parity of $k$, the even multipliers reduce to smaller cases by Sylvester doubling, $H_{2m}=H_2\otimes H_m$, so the whole content of the conjecture sits in the odd multipliers — which is what this statement isolates. The smallest order with no known Hadamard matrix is $4\cdot167=668$; the conjecture has been verified for every $k$ below that.
--
--   Paley's constructions settle $k$ whenever $4k-1$ or $4k/2-1$ is a prime power of the right residue, and Williamson's method settles many more, but no construction is known to cover all odd $k$, and none is expected without new ideas.
-- source:
--   J. Hadamard, Resolution d'une question relative aux determinants, Bull. Sci. Math. 17 (1893) 240-246; R. E. A. C. Paley, On orthogonal matrices, J. Math. Phys. 12 (1933) 311-320; J. Williamson, Hadamard's determinant theorem and the sum of four squares, Duke Math. J. 11 (1944) 65-81. Orthogonality restatement of Hadamard.odd_multiplier_exists.

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open Matrix

theorem Hadamard.exists_orthogonal_pm_one (k : ℕ) (hk : Odd k) :
    ∃ M : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ,
      (∀ i j, M i j ∈ ({1, -1} : Finset ℝ)) ∧
      M * Mᵀ = ((4 * k : ℕ) : ℝ) • (1 : Matrix (Fin (4 * k)) (Fin (4 * k)) ℝ) := by sorry
