-- Prove2me | Theorems.Thm_mme_coupled_left_half_filtered_power_restriction
-- name    : mme_coupled_left_half_filtered_power_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:10:38.055552+00:00
-- url     : https://prove2.me/theorems/f5ba0945-7463-4cf5-955d-e1885d4072d2
-- title:
--   Left-half word filters return to the original X mode
-- statement:
--   Let $C_q$ be the coupled Coppersmith–Winograd tensor over a field, let $\rho$ cyclically permute its three modes, and let $n\ge0$. Choose any set $P$ of words of length $n$ over the two $q$-coordinate families. In $(\rho^2 C_q)^{\otimes n}$ retain exactly these words in mode 2 and then apply $\rho$. The resulting tensor restricts to $C_q^{\otimes n}$ with precisely the same word filter in mode 0. The other two modes remain unfiltered, and every numeric coordinate of every retained word is preserved.
-- source:
--   Basis-preserving cyclic transport of the coupled tensor, word-basis transport to powers, and the common-halving reoriented source restriction.

import Theorems.Thm_mme_permutation_modewise_map_eq
import Theorems.Thm_mme_permuted_power_word_basis_transport
import Definitions.Def_mme_CW_coupled_value

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_coupled_left_half_filtered_power_restriction
    {K : Type u} [Field K] (q n : ℕ)
    (keep : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) n → Prop) [DecidablePred keep] :
    let C := coupledObj K q
    let S := (TensorObj.permObj (cyclicPerm.trans cyclicPerm) C).kronPow n
    let T := C.kronPow n
    let b := (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
    let bs := kronPowModeBasis (TensorObj.permObj (cyclicPerm.trans cyclicPerm) C) 2 b n
    let bt := kronPowModeBasis C 0 b n
    let fs : ∀ i, S.V i →ₗ[K] S.V i := Function.update (fun _ => LinearMap.id) 2
      (bs.constr K (fun w => if keep w then bs w else 0))
    let ft : ∀ i, T.V i →ₗ[K] T.V i := Function.update (fun _ => LinearMap.id) 0
      (bt.constr K (fun w => if keep w then bt w else 0))
    TensorObj.Restrict { T with t := PiTensorProduct.map ft T.t }
      (TensorObj.permObj cyclicPerm { S with t := PiTensorProduct.map fs S.t }) := by sorry
