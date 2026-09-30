-- Prove2me | solution 1 for lean_workbook_plus_18918
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:04:06.318055+00:00
-- url     : https://prove2.me/submissions/14901627-2cea-4361-bc0d-c00a2c4eff36

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Order.Interval.Finset.Nat
import Lean.Elab.Tactic.Omega

namespace DivisibilityPigeonhole

def oddPart (a : ℕ) : ℕ := ordCompl[2] a

def key (a : ℕ) : ℕ := oddPart a / 2

theorem oddPart_eq_key (a : ℕ) (ha : 0 < a) : oddPart a = 2 * key a + 1 := by
  have hnot : ¬2 ∣ oddPart a := Nat.not_dvd_ordCompl Nat.prime_two ha.ne'
  have hmod : oddPart a % 2 ≠ 0 := by
    intro h
    exact hnot (Nat.dvd_iff_mod_eq_zero.mpr h)
  have hlt := Nat.mod_lt (oddPart a) (by decide : 0 < 2)
  dsimp [key]
  omega

theorem same_key_comparable (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hkey : key a = key b) : a ∣ b ∨ b ∣ a := by
  have hodd : oddPart a = oddPart b := by
    rw [oddPart_eq_key a ha, oddPart_eq_key b hb, hkey]
  have haeq : a = 2 ^ a.factorization 2 * oddPart a :=
    (Nat.ordProj_mul_ordCompl_eq_self a 2).symm
  have hbeq : b = 2 ^ b.factorization 2 * oddPart b :=
    (Nat.ordProj_mul_ordCompl_eq_self b 2).symm
  rcases le_total (a.factorization 2) (b.factorization 2) with hab | hba
  · left
    rw [haeq, hbeq, hodd]
    exact mul_dvd_mul_right (pow_dvd_pow 2 hab) _
  · right
    rw [haeq, hbeq, hodd]
    exact mul_dvd_mul_right (pow_dvd_pow 2 hba) _

theorem antichain_card_bound (n : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 2 * n)
    (hanti : ∀ a ∈ S, ∀ b ∈ S, a ∣ b → a = b) : S.card ≤ n := by
  let encode : S → Fin n := fun a => ⟨key a, by
    have hk := oddPart_eq_key a (hS a a.property).1
    have hle : oddPart a ≤ a := Nat.ordCompl_le a 2
    have hb := (hS a a.property).2
    omega⟩
  have hinj : Function.Injective encode := by
    intro a b heq
    have hk : key a = key b := congrArg Fin.val heq
    apply Subtype.ext
    rcases same_key_comparable a b (hS a a.property).1 (hS b b.property).1 hk with hab | hba
    · exact hanti a a.property b b.property hab
    · exact (hanti b b.property a a.property hba).symm
  have hcount := Fintype.card_le_of_injective encode hinj
  simpa using hcount

theorem distinct_divisibility_pair (n : ℕ) (S : Finset ℕ)
    (hS : ∀ a ∈ S, 0 < a ∧ a ≤ 2 * n) (hcard : n + 1 ≤ S.card) :
    ∃ x ∈ S, ∃ y ∈ S, x < y ∧ x ∣ y := by
  classical
  by_contra hnone
  have hanti : ∀ a ∈ S, ∀ b ∈ S, a ∣ b → a = b := by
    intro a ha b hb hab
    by_contra hne
    have hle := Nat.le_of_dvd (hS b hb).1 hab
    have hlt : a < b := by omega
    exact hnone ⟨a, ha, b, hb, hlt, hab⟩
  have hbound := antichain_card_bound n S hS hanti
  omega

theorem upper_half_antichain (n : ℕ) (a b : ℕ)
    (ha : a ∈ Finset.Ioc n (2 * n)) (hb : b ∈ Finset.Ioc n (2 * n))
    (hab : a ∣ b) : a = b := by
  have ha' := Finset.mem_Ioc.mp ha
  have hb' := Finset.mem_Ioc.mp hb
  by_contra hne
  obtain ⟨k, hk⟩ := hab
  have hk0 : k ≠ 0 := by
    intro h
    subst k
    simp only [Nat.mul_zero] at hk
    omega
  have hk1 : k ≠ 1 := by
    intro h
    subst k
    simp only [Nat.mul_one] at hk
    exact hne hk.symm
  have hprod := Nat.mul_le_mul_left a (show 2 ≤ k by omega)
  omega

theorem sharp_antichain_bound (n : ℕ) :
    ∃ S : Finset ℕ, S.card = n ∧
      (∀ a ∈ S, 0 < a ∧ a ≤ 2 * n) ∧
      (∀ a ∈ S, ∀ b ∈ S, a ∣ b → a = b) := by
  refine ⟨Finset.Ioc n (2 * n), ?_, ?_, ?_⟩
  · rw [Nat.card_Ioc]
    omega
  · intro a ha
    have := Finset.mem_Ioc.mp ha
    omega
  · intro a ha b hb hab
    exact upper_half_antichain n a b ha hb hab

theorem full_written (n : ℕ) (S : Finset ℕ)
    (hS : S ⊆ Finset.Icc 1 (2 * n)) (hcard : n + 1 ≤ S.card) :
    ∃ x ∈ S, ∃ y ∈ S, x < y ∧ x ∣ y := by
  apply distinct_divisibility_pair n S ?_ hcard
  intro a ha
  have := Finset.mem_Icc.mp (hS ha)
  omega

end DivisibilityPigeonhole

theorem solution (n : ℕ) (_hn : 0 < n) (A : Finset ℕ)
    (hA : A = Finset.Icc 1 (2 * n)) (S : Finset ℕ) (hS : S ⊆ A)
    (hS' : n + 1 ≤ S.card) : ∃ x ∈ S, ∃ y ∈ S, x ∣ y := by
  subst A
  obtain ⟨x, hx, y, hy, _, hxy⟩ := DivisibilityPigeonhole.full_written n S hS hS'
  exact ⟨x, hx, y, hy, hxy⟩
