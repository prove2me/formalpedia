-- Prove2me | Theorems.Thm_mme_dwz_q6_common_halving_union_word_projection_restriction
-- name    : mme_dwz_q6_common_halving_union_word_projection_restriction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T02:49:55.586125+00:00
-- url     : https://prove2.me/theorems/a216c65d-3587-45a1-bd21-3248dfbb1d44
-- title:
--   The aggregate union of family half-words restricts from the allowed-word source
-- statement:
--   Let $K$ be a field, $s\in\{13,14\}$ a Table-2 component row, $m\geq0$, and $N=c_s m$. Fix a primary hash family with a common balanced $X,Y$ halving, and write
--   $$W=(\pi^2 C_6)^{\otimes N}\otimes(\pi C_6)^{\otimes N}.$$
--   Let $U_X$ be the union of the family's first-half $X$ words, and $U_Y$ the union of its second-half $Y$ words. On the third-mode product basis of $W$, retain a pair of words exactly when its first binary-label word lies in $U_X$ and its second lies in $U_Y$; retain every numerical letter. Let $P$ be this coordinate projector, with identity maps on the other modes. Then the tensor $P(W)$ restricts from the literal allowed-word row-$s$ component power paired with its $X,Y$-swapped copy.
--
--   This is a single aggregate projection: it keeps all pairs in $U_X\times U_Y$, including pairs whose two words come from different family entries. It assumes neither an induced selection nor a coloring. The theorem establishes access to this projected source; it does not identify it with a matrix tensor or assert a quantitative extraction bound.
-- source:
--   Concrete aggregate application of the canonical source routers and common-halving profile-mismatch criterion for the source-faithful DWZ 121/211 component setup.

import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Definitions.Def_mme_dwz_component_pair_projection_data
import Definitions.Def_mme_kron_pow_mode_word_basis
open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction Module TensorProduct
universe u
set_option autoImplicit false

theorem mme_dwz_q6_common_halving_union_word_projection_restriction
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let left := (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N
    let right := (TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N
    let paired := TensorObj.kron left right
    let bX := kronPowModeBasis
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)) 2
      ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N
    let bY := kronPowModeBasis (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
      ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N
    let basis := bX.tensorProduct bY
    let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x ↦ Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) x.down
    let allowed := fun w : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N ×
        PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N ↦
      (∃ p : Fin A × Fin H, ∀ r,
        grade (PowIndex.get N w.1 r) =
          (family.entry p).val 0 (halving.position (Sum.inl r))) ∧
      (∃ p : Fin A × Fin H, ∀ r,
        grade (PowIndex.get N w.2 r) =
          (family.entry p).val 1 (halving.position (Sum.inr r)))
    letI : DecidablePred allowed := Classical.decPred _
    let projection : ∀ i, paired.V i →ₗ[K] paired.V i :=
      Function.update (fun _ ↦ LinearMap.id) 2
        (basis.constr K (fun w ↦ if allowed w then basis w else 0))
    TensorObj.Restrict { paired with t := PiTensorProduct.map projection paired.t }
      (componentPairRestricted K s m) := by sorry
