-- Prove2me | Definitions.Def_mme_cyclicSymmetrization_public_perm
-- name    : mme_cyclicSymmetrization_public_perm
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-08-25T03:23:14.727052+00:00
-- url     : https://prove2.me/theorems/2d51e15d-29ea-4679-a0aa-11602b14e30d
-- title:
--   Cyclic symmetrization via the public cyclic mode permutation
-- statement:
--   The mode-relabeling operation used in the definition of cyclic symmetrization is definitionally the public tensor mode-permutation operation. Moreover, the private three-cycle occurring in the original cyclic-symmetrization definition agrees with the public cyclic permutation. Hence, for every order-three tensor $T$,
--
--   $$
--   \operatorname{cyc}(T)=T\otimes\pi(T)\otimes\pi^2(T),
--   $$
--
--   with both permuted factors expressed using the public permutation API. This equality makes the generic permutation-grading and Kronecker-grading interfaces directly applicable to cyclic symmetrizations.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), symmetric-value definition on journal p. 264, https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_permutation

open MME

universe u

theorem permuteModes_eq_permObj
    {K : Type u} [Field K] (e : Equiv.Perm (Fin 3))
    (T : TensorObj K 3) :
    permuteModes e T = TensorObj.permObj e T := by
  rfl

theorem cyclicSymmetrization_eq_public_perm
    {K : Type u} [Field K] (T : TensorObj K 3) :
    cyclicSymmetrization T =
      TensorObj.kron T
        (TensorObj.kron
          (TensorObj.permObj cyclicPerm T)
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) T)) := by
  rw [← permuteModes_eq_permObj cyclicPerm T,
    ← permuteModes_eq_permObj (cyclicPerm.trans cyclicPerm) T]
  unfold cyclicSymmetrization
  congr 3
  · apply Equiv.ext
    intro i
    fin_cases i <;> rfl
  · apply Equiv.ext
    intro i
    fin_cases i <;> rfl


