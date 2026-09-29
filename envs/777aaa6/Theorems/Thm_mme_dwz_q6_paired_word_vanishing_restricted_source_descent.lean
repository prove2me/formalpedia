-- Prove2me | Theorems.Thm_mme_dwz_q6_paired_word_vanishing_restricted_source_descent
-- name    : mme_dwz_q6_paired_word_vanishing_restricted_source_descent
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T02:44:59.316107+00:00
-- url     : https://prove2.me/theorems/8de67f4e-d108-4937-bc25-a238d8212d34
-- title:
--   Paired word vanishing gives descent to the restricted 121 and 211 sources
-- statement:
--   Let $K$ be a field, let $s\in\{13,14\}$ be the Table-2 row for the 121 or 211 component, and let $N=c_s m$. Fix a primary hash family with a common balanced $X,Y$ halving. Suppose coordinate maps restrict the paired oriented coupled powers
--   $$ (\pi^2 C_6)^{\otimes N}\otimes(\pi C_6)^{\otimes N} $$
--   to a tensor $T$. Assume that the third coordinate map kills every pair of basis words for which either the first binary-label word occurs in none of the family's first-half $X$ addresses or the second occurs in none of its second-half $Y$ addresses. Then $T$ restricts from the literal pair of allowed-word component powers: the restricted row-$s$ power tensored with its $X,Y$-swapped copy.
--
--   The conclusion retains the same target tensor $T$. The hypothesis concerns the full coordinate map and does not require the family to admit an induced selection. Constructing a target map with the required vanishing and proving its quantitative matrix-volume bound remain separate tasks.
-- source:
--   General source-compatibility lemma for the source-faithful DWZ 121/211 component setup: canonical basis-labelled routers and the common-halving profile mismatch criterion.

import Theorems.Thm_mme_dwz_q6_canonical_121_211_paired_powered_basis_labelled_source_router
import Theorems.Thm_mme_dwz_q6_121_211_common_halving_disallowed_word_mismatches_halves
import Theorems.Thm_mme_dwz_q6_canonical_121_swap_power_to_211_basis_transport
import Theorems.Thm_mme_dwz_q6_canonical_211_swap_power_to_121_basis_transport
import Theorems.Thm_mme_dwz_component_pair_restriction_of_disallowed_word_vanishing
import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data

open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction
open Module TensorProduct
universe u
set_option autoImplicit false

theorem mme_dwz_q6_paired_word_vanishing_restricted_source_descent
    {K : Type u} [Field K] {N L G A H : ℕ}
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m : ℕ)
    (hN : N = DWZTable2Counts.component s * m)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (T : TensorObj K 3)
    (maps : ∀ i, (TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).V i →ₗ[K] T.V i)
    (htensor : PiTensorProduct.map maps (TensorObj.kron
      ((TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)).kronPow N)
      ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).t = T.t)
    (hzero : ∀ (wX wY : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N),
    let grade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x ↦ Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) x.down
    ((¬ ∃ p : Fin A × Fin H, ∀ r,
      grade (PowIndex.get N wX r) =
        (family.entry p).val 0 (halving.position (Sum.inl r))) ∨
     (¬ ∃ p : Fin A × Fin H, ∀ r,
      grade (PowIndex.get N wY r) =
        (family.entry p).val 1 (halving.position (Sum.inr r)))) →
    maps 2 (kronPowModeBasis
        (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)) 2
        ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N wX ⊗ₜ[K]
      kronPowModeBasis (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
        ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N wY) = 0) :
    TensorObj.Restrict T (componentPairRestricted K s m) := by sorry
