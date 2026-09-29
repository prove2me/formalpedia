-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_survivors_assemble_MM
-- name    : mme_CW_q6_coupled_survivors_assemble_MM
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:32:26.336521+00:00
-- url     : https://prove2.me/theorems/4f9a0487-e091-4639-b23e-a4fb03923a36
-- title:
--   Mode-disjoint coupled survivors assemble into square matrix products
-- statement:
--   Let $L,G,k$ be nonnegative integers. A symmetrized coupled survivor contains $2G$ high blocks and $2L$ low blocks. Each high block restricts to $\langle36,36,36\rangle$ and each low block to $\langle6,6,6\rangle$, so one survivor restricts to
--
--   $$
--   \left\langle36^{2G}6^{2L},\;36^{2G}6^{2L},\;36^{2G}6^{2L}\right\rangle
--   =\left\langle6^{4G+2L},6^{4G+2L},6^{4G+2L}\right\rangle.
--   $$
--
--   Consequently a direct sum of $k$ mode-disjoint survivors restricts componentwise to the direct sum of $k$ copies of this square matrix-multiplication tensor. This is the tensor-assembly step after Salem--Spencer hashing and collision pruning have already produced the survivor family.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), coupled fine-structure calculation `(q^2)^(2G) q^(2L) = q^(4G+2L)` and disjoint C-tensor objects on journal p. 271 (PDF p. 21); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_tensor_rank
open MME
universe u

theorem mme_CW_q6_coupled_survivors_assemble_MM
    {K : Type u} [Field K] (L G k : ℕ) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin k =>
        MMObj K
          (36 ^ (2 * G) * 6 ^ (2 * L))
          (36 ^ (2 * G) * 6 ^ (2 * L))
          (36 ^ (2 * G) * 6 ^ (2 * L))))
      (TensorObj.bigAdd (fun _ : Fin k => coupledQ6Survivor K L G)) := by sorry
