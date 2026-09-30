-- Prove2me | solution 1 for lean_workbook_plus_78452
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:16:06.629921+00:00
-- url     : https://prove2.me/submissions/9ab13792-3294-4071-9c7f-80f706f0411c

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

private lemma same_odd_part_comparable (a b : ℕ) (h : ordCompl[2] a = ordCompl[2] b) :
    a ∣ b ∨ b ∣ a := by
  rcases le_total (a.factorization 2) (b.factorization 2) with hab | hba
  · left
    have hd := mul_dvd_mul (pow_dvd_pow 2 hab) (dvd_of_eq h)
    simpa only [Nat.ordProj_mul_ordCompl_eq_self] using hd
  · right
    have hd := mul_dvd_mul (pow_dvd_pow 2 hba) (dvd_of_eq h.symm)
    simpa only [Nat.ordProj_mul_ordCompl_eq_self] using hd

private lemma distinct_divisibility_pair (n : ℕ) (A : Finset ℕ) (hA : A.card = n+1)
    (hA2 : ∀ a ∈ A, 0 < a ∧ a ≤ 2*n) :
    ∃ a b, a ∈ A ∧ b ∈ A ∧ a ≠ b ∧ a ∣ b := by
  classical
  have hodd (a : A) : ordCompl[2] a.val % 2 = 1 := by
    have h := Nat.not_dvd_ordCompl (by decide : Nat.Prime 2) (hA2 a.val a.property).1.ne'
    rw [Nat.dvd_iff_mod_eq_zero] at h
    omega
  let color : A → Fin n := fun a => ⟨ordCompl[2] a.val / 2, by
    have hle := (Nat.ordCompl_le a.val 2).trans (hA2 a.val a.property).2
    have ho := hodd a
    omega⟩
  have hnot : ¬Function.Injective color := by
    intro hinj
    have hcard := Fintype.card_le_of_injective color hinj
    simp only [Fintype.card_coe, Fintype.card_fin, hA] at hcard
    omega
  unfold Function.Injective at hnot
  push_neg at hnot
  obtain ⟨a, b, heq, hne⟩ := hnot
  have hparts : ordCompl[2] a.val = ordCompl[2] b.val := by
    have hc : ordCompl[2] a.val / 2 = ordCompl[2] b.val / 2 := congrArg Fin.val heq
    have ha := hodd a
    have hb := hodd b
    omega
  have hne' : a.val ≠ b.val := fun h => hne (Subtype.ext h)
  rcases same_odd_part_comparable a.val b.val hparts with hab | hba
  · exact ⟨a.val, b.val, a.property, b.property, hne', hab⟩
  · exact ⟨b.val, a.val, b.property, a.property, hne'.symm, hba⟩

theorem solution (n : ℕ) (hn : 0 < n) (A : Finset ℕ) (hA : A.card = n+1)
    (hA2 : ∀ a ∈ A, 0 < a ∧ a ≤ 2*n) : ∃ a b, a ∈ A ∧ b ∈ A ∧ a ∣ b := by
  obtain ⟨a, b, ha, hb, _, hd⟩ := distinct_divisibility_pair n A hA hA2
  exact ⟨a, b, ha, hb, hd⟩
