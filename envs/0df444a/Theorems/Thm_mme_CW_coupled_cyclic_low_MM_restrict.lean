-- Prove2me | Theorems.Thm_mme_CW_coupled_cyclic_low_MM_restrict
-- name    : mme_CW_coupled_cyclic_low_MM_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:57:30.003508+00:00
-- url     : https://prove2.me/theorems/7758fe51-dd4d-4dc0-8ce5-49144ca4fe5f
-- title:
--   The cyclic low block is square matrix multiplication of side $q$
-- statement:
--   The matrix-multiplication block $\langle1,q,1\rangle$ has cyclic copies $\langle1,1,q\rangle$ and $\langle q,1,1\rangle$. Their Kronecker product is
--
--   $$
--   \langle1,q,1\rangle\otimes\langle1,1,q\rangle\otimes\langle q,1,1\rangle
--   \cong\langle q,q,q\rangle.
--   $$
--
--   Consequently $\langle q,q,q\rangle$ is a concrete restriction of the cyclic symmetrization of $\langle1,q,1\rangle$. Its matrix-product volume is $q^3$, giving one of the eight low-weight terms in the coupled constituent's raw value.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), symmetric value on journal p. 264 and the low-volume coupled blocks in the lemma on journal pp. 270--272 (PDF pp. 14, 20--22); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_permutation
open MME
universe u

theorem mme_CW_coupled_cyclic_low_MM_restrict
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K q q q)
      (cyclicSymmetrization (MMObj K 1 q 1)) := by sorry
