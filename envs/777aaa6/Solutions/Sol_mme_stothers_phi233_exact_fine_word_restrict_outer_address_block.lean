-- Prove2me | solution 1 for mme_stothers_phi233_exact_fine_word_restrict_outer_address_block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:21:42.395524+00:00
-- url     : https://prove2.me/submissions/a1e802e3-b565-4a65-8bdf-093844428dad

import Mathlib.Tactic
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_stothers_phi233_exact_label
import Theorems.Thm_mme_stothers_phi233_fine_source_restrict_outer_block

open MME

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem kron_restrict
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d)
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X')
    (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y) (TensorObj.kron X' Y') := by
  rw [← TensorQ.le_toQ]
  let P := TensorQ.tensorStrassen K d hd
  have hx : P.le (TensorQ.toQ X) (TensorQ.toQ X') := hX
  have hy : P.le (TensorQ.toQ Y) (TensorQ.toQ Y') := hY
  exact P.le_trans _ _ _ (P.mul_right _ _ hx _)
    (by simpa only [mul_comm] using P.mul_right _ _ hy (TensorQ.toQ X'))

private theorem kronFin_restrict
    {K : Type u} [Field K] {d : ℕ} (hd : 1 < d) :
    ∀ (n : ℕ) (X Y : Fin n → TensorObj K d),
      (∀ r, TensorObj.Restrict (X r) (Y r)) →
      TensorObj.Restrict (TensorObj.kronFin n X)
        (TensorObj.kronFin n Y) := by
  intro n
  induction n with
  | zero =>
      intro X Y _
      exact TensorObj.Restrict.refl _
  | succ n ih =>
      intro X Y h
      change TensorObj.Restrict
        (TensorObj.kron (X 0)
          (TensorObj.kronFin n (fun r ↦ X r.succ)))
        (TensorObj.kron (Y 0)
          (TensorObj.kronFin n (fun r ↦ Y r.succ)))
      exact kron_restrict hd (h 0)
        (ih (fun r ↦ X r.succ) (fun r ↦ Y r.succ)
          (fun r ↦ h r.succ))

theorem solution
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi233.fineSourceObj K q
          (MME.StothersFourth.Phi233.exactLabelAt address j)))
      (gradedAddressBlock
        (MME.StothersFourth.Phi233.outerGrading K q) address.1.1) := by
  have h := kronFin_restrict (K := K) (d := 3) (by omega)
    (2 * N)
    (fun j ↦ MME.StothersFourth.Phi233.fineSourceObj K q
      (MME.StothersFourth.Phi233.exactLabelAt address j))
    (fun j ↦
      (MME.StothersFourth.Phi233.outerGrading K q).blockSubtensor
        (MME.StothersFourth.Phi233.pattern
          (MME.StothersFourth.Phi233.exactLabelAt address j)))
    (fun j ↦ mme_stothers_phi233_fine_source_restrict_outer_block
      (K := K) q (MME.StothersFourth.Phi233.exactLabelAt address j))
  change TensorObj.Restrict _
    (TensorObj.kronFin (2 * N) (fun j ↦
      (MME.StothersFourth.Phi233.outerGrading K q).blockSubtensor
        (fun i ↦ address.1.1 i j)))
  have hfamily :
      (fun j : Fin (2 * N) ↦
        (MME.StothersFourth.Phi233.outerGrading K q).blockSubtensor
          (fun i ↦ address.1.1 i j)) =
      (fun j : Fin (2 * N) ↦
        (MME.StothersFourth.Phi233.outerGrading K q).blockSubtensor
          (MME.StothersFourth.Phi233.pattern
            (MME.StothersFourth.Phi233.exactLabelAt address j))) := by
    funext j
    congr 1
    exact MME.StothersFourth.Phi233.addressType_exactLabelAt address j
  rw [hfamily]
  exact h
