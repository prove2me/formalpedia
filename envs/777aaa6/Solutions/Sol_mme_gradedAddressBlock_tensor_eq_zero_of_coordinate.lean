-- Prove2me | solution 1 for mme_gradedAddressBlock_tensor_eq_zero_of_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T14:28:31.060486+00:00
-- url     : https://prove2.me/submissions/65e1aa20-3366-4a96-9497-63a44ba5cd5c

import Definitions.Def_mme_induced_word_zeroing

open MME PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t R : ℕ}
    (G : T.TypeGrading t) (address : Fin 3 → Fin R → Fin t)
    (r : Fin R)
    (hr : G.blockTensor (fun i ↦ address i r) = 0) :
    (gradedAddressBlock G address).t = 0 := by
  induction R with
  | zero => exact Fin.elim0 r
  | succ R ih =>
      refine Fin.cases
        (motive := fun r ↦
          G.blockTensor (fun i ↦ address i r) = 0 →
            (gradedAddressBlock G address).t = 0)
        ?_ (fun r' ↦ ?_) r hr
      · intro hr0
        change interchange (G.blockTensor (fun i ↦ address i 0))
            (gradedAddressBlock G
              (fun i j ↦ address i j.succ)).t = 0
        rw [hr0]
        simp only [map_zero, LinearMap.zero_apply]
      · intro hr'
        change interchange (G.blockTensor (fun i ↦ address i 0))
            (gradedAddressBlock G
              (fun i j ↦ address i j.succ)).t = 0
        have htail :
            (gradedAddressBlock G
              (fun i j ↦ address i j.succ)).t = 0 :=
          ih (fun i j ↦ address i j.succ) r' hr'
        rw [htail]
        exact LinearMap.map_zero _
