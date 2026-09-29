-- Prove2me | Theorems.Thm_mme_CW_coupled_cyclic_high_MM_restrict
-- name    : mme_CW_coupled_cyclic_high_MM_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T04:53:30.651813+00:00
-- url     : https://prove2.me/theorems/300653e9-b9d8-452e-a56d-17fb4f5bd304
-- title:
--   The cyclic high block is square matrix multiplication of side $q^2$
-- statement:
--   The matrix-multiplication block $\langle q,1,q\rangle$ has cyclic copies $\langle q,q,1\rangle$ and $\langle1,q,q\rangle$. Their Kronecker product is the square matrix-multiplication tensor
--
--   $$
--   \langle q,1,q\rangle\otimes\langle q,q,1\rangle\otimes\langle1,q,q\rangle
--   \cong\langle q^2,q^2,q^2\rangle.
--   $$
--
--   Consequently $\langle q^2,q^2,q^2\rangle$ is a concrete restriction of the cyclic symmetrization of $\langle q,1,q\rangle$. Its matrix-product volume is $q^6$, giving one of the four high-weight terms in the coupled constituent's raw value.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), symmetric value on journal p. 264 and the high-volume coupled block in the lemma on journal pp. 270--272 (PDF pp. 14, 20--22); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_permutation
open MME
universe u

theorem mme_CW_coupled_cyclic_high_MM_restrict
    {K : Type u} [Field K] (q : ℕ) :
    TensorObj.Restrict
      (MMObj K (q * q) (q * q) (q * q))
      (cyclicSymmetrization (MMObj K q 1 q)) := by sorry
