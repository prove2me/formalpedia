-- Prove2me | solution 1 for mme_gradedAddressBlock_reindex_perm_iso
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T07:54:08.720941+00:00
-- url     : https://prove2.me/submissions/a1121bf3-61ca-4b7a-b0c7-fc2bd236f840

import Theorems.Thm_mme_kronFin_group_by_exact_fibers_iso
import Definitions.Def_mme_induced_word_zeroing

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K] {T : TensorObj K 3} {t N : ℕ}
    (G : T.TypeGrading t) (address : Fin 3 → Fin N → Fin t)
    (e : Equiv.Perm (Fin N)) :
    TensorObj.Isomorphic
      (gradedAddressBlock G (fun i r ↦ address i (e r)))
      (gradedAddressBlock G address) := by
  classical
  let X : Fin N → TensorObj K 3 := fun r ↦
    G.blockSubtensor (fun i ↦ address i r)
  let multiplicity : Fin N → ℕ := fun s ↦
    Fintype.card {r : Fin N // r = s}
  have hperm : ∀ s : Fin N,
      Fintype.card {r : Fin N // e r = s} = multiplicity s := by
    intro s
    exact Fintype.card_congr
      (Equiv.subtypeEquiv e (fun _ ↦ Iff.rfl))
  have hsource := mme_kronFin_group_by_exact_fibers_iso
    X e multiplicity hperm
  have htarget := mme_kronFin_group_by_exact_fibers_iso
    X (fun r ↦ r) multiplicity (fun s ↦ by
      simp [multiplicity])
  change TensorObj.Isomorphic
    (TensorObj.kronFin N (fun r ↦ X (e r)))
    (TensorObj.kronFin N (fun r ↦ X r))
  exact TensorObj.Isomorphic.trans hsource htarget.symm
