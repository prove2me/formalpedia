-- Prove2me | Theorems.Thm_complex_posSemidef_det_le_prod_diag_re
-- name    : complex_posSemidef_det_le_prod_diag_re
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T20:33:51.431717+00:00
-- url     : https://prove2.me/theorems/7a2d4bae-9246-4eb2-b88a-52c9e5a5fe75
-- title:
--   Hadamard bound for complex positive semidefinite matrices
-- statement:
--   For a finite complex Hermitian positive semidefinite matrix $M$, the Hadamard determinant inequality states
--
--   $$
--   \operatorname{Re}(\det M) \le \prod_{i \in I} \operatorname{Re}(M_{ii}).
--   $$
--
--   For positive semidefinite $M$, its determinant and diagonal entries are real and nonnegative, so this bounds its determinant by the product of its diagonal entries. This reusable inequality applies in particular to Gram matrices.
--
--   **Formalization Note** The theorem states the bound in `Real` using the real parts of the complex determinant and diagonal entries.
-- source:
--   Hadamard determinant inequality for positive semidefinite Hermitian matrices

import Mathlib.Analysis.Matrix.PosDef
open scoped ComplexOrder

theorem complex_posSemidef_det_le_prod_diag_re {idx : Type*} [Fintype idx] [DecidableEq idx] (M : Matrix idx idx Complex) (hM : M.PosSemidef) : (M.det.re : Real) <= Finset.prod Finset.univ (fun i : idx => ((M i i).re : Real)) := by sorry
