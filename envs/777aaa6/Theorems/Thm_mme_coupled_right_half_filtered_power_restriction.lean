-- Prove2me | Theorems.Thm_mme_coupled_right_half_filtered_power_restriction
-- name    : mme_coupled_right_half_filtered_power_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T05:10:36.465676+00:00
-- url     : https://prove2.me/theorems/ac7f3a06-d1e7-4358-b2ca-7bd480dbd927
-- title:
--   Right-half word filters return to the original Y mode
-- statement:
--   Let $C_q$ be the coupled Coppersmith–Winograd tensor over a field, let $\rho$ cyclically permute its three modes, and let $n\ge0$. Choose any set $P$ of words of length $n$ over the two $q$-coordinate families. In $(\rho C_q)^{\otimes n}$ retain exactly these words in mode 2 and then apply $\rho^2$. The resulting tensor restricts to $C_q^{\otimes n}$ with precisely the same word filter in mode 1. The other two modes remain unfiltered, and every numeric coordinate of every retained word is preserved.
-- source:
--   Basis-preserving cyclic transport of the coupled tensor, word-basis transport to powers, and the common-halving reoriented source restriction.

import Theorems.Thm_mme_permutation_modewise_map_eq
import Theorems.Thm_mme_permuted_power_word_basis_transport
import Definitions.Def_mme_CW_coupled_value

open MME MME.DWZComponentRestriction Module TensorProduct PiTensorProduct
universe u
set_option autoImplicit false

theorem mme_coupled_right_half_filtered_power_restriction
    {K : Type u} [Field K] (q n : ℕ)
    (keep : PowIndex (ULift.{u} (Fin q ⊕ Fin q)) n → Prop) [DecidablePred keep] :
    let C := coupledObj K q
    let S := (TensorObj.permObj cyclicPerm C).kronPow n
    let T := C.kronPow n
    let b := (Pi.basisFun K (Fin q ⊕ Fin q)).reindex Equiv.ulift.symm
    let bs := kronPowModeBasis (TensorObj.permObj cyclicPerm C) 2 b n
    let bt := kronPowModeBasis C 1 b n
    let fs : ∀ i, S.V i →ₗ[K] S.V i := Function.update (fun _ => LinearMap.id) 2
      (bs.constr K (fun w => if keep w then bs w else 0))
    let ft : ∀ i, T.V i →ₗ[K] T.V i := Function.update (fun _ => LinearMap.id) 1
      (bt.constr K (fun w => if keep w then bt w else 0))
    TensorObj.Restrict { T with t := PiTensorProduct.map ft T.t }
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) { S with t := PiTensorProduct.map fs S.t }) := by sorry
