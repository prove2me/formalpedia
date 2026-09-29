-- Prove2me | solution 1 for mme_stothers_phi233_exact_fine_source_restrict_coarse_power
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:06:26.324872+00:00
-- url     : https://prove2.me/submissions/0562b904-4347-41d6-ad0c-9700688965d4

import Mathlib.Tactic
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_stothers_phi233_exact_label
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_CW_fourth_fine_block_restrict_coarse

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

private theorem kronFin_const_eq_kronPow
    {K : Type u} [Field K] {d : ℕ}
    (T : TensorObj K d) :
    ∀ n : ℕ, TensorObj.kronFin n (fun _ ↦ T) = T.kronPow n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      change TensorObj.kron T
          (TensorObj.kronFin n (fun _ ↦ T)) =
        TensorObj.kron T (T.kronPow n)
      rw [ih]

theorem solution
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (address : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) :
    TensorObj.Restrict
      (TensorObj.kronFin (2 * N) (fun j ↦
        MME.StothersFourth.Phi233.fineSourceObj K q
          (MME.StothersFourth.Phi233.exactLabelAt address j)))
      ((MME.StothersFourth.cwFourthConstituent K q 2 3 3).kronPow
        (2 * N)) := by
  have hcomponent : ∀ r : Fin 10,
      TensorObj.Restrict
        (MME.StothersFourth.Phi233.fineSourceObj K q r)
        (MME.StothersFourth.cwFourthConstituent K q 2 3 3) := by
    intro r
    fin_cases r
    all_goals
      apply mme_CW_fourth_fine_block_restrict_coarse q
      intro s
      fin_cases s <;> rfl
  have h := kronFin_restrict (K := K) (d := 3) (by omega)
    (2 * N)
    (fun j ↦ MME.StothersFourth.Phi233.fineSourceObj K q
      (MME.StothersFourth.Phi233.exactLabelAt address j))
    (fun _ ↦ MME.StothersFourth.cwFourthConstituent K q 2 3 3)
    (fun j ↦ hcomponent
      (MME.StothersFourth.Phi233.exactLabelAt address j))
  simpa only [kronFin_const_eq_kronPow] using h
