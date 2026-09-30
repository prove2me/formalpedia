-- Prove2me | solution 1 for lean_workbook_plus_9405
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T00:47:07.252279+00:00
-- url     : https://prove2.me/submissions/0d945fba-8320-49f2-93ad-c4ee7e48b615

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Data.Int.NatAbs
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace PellFiveFourClassification

def state : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | n + 1 => ((state n).1 + (state n).2, (state n).1 + 2 * (state n).2)

theorem state_norm (n : ℕ) :
    (state n).1 ^ 2 + (state n).1 * (state n).2 = (state n).2 ^ 2 + 1 := by
  induction n with
  | zero => decide
  | succ n ih =>
      simp only [state]
      nlinarith

theorem first_positive (n : ℕ) : 0 < (state n).1 := by
  have h := state_norm n
  by_contra hn
  have hz : (state n).1 = 0 := by omega
  simp [hz] at h

theorem second_strictMono : StrictMono (fun n => (state n).2) := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h := first_positive n
  simp only [state]
  omega

theorem norm_descent (a b : ℕ) (hb : 0 < b)
    (h : a ^ 2 + a * b = b ^ 2 + 1) :
    0 < a ∧ a ≤ b ∧ b < 2 * a ∧
      (2 * a - b) ^ 2 + (2 * a - b) * (b - a) = (b - a) ^ 2 + 1 := by
  have ha : 0 < a := by
    by_contra hn
    have hz : a = 0 := by omega
    simp [hz] at h
  have hab : a ≤ b := by
    by_contra hn
    have hba : b + 1 ≤ a := by omega
    nlinarith [Nat.mul_self_le_mul_self hba, Nat.mul_le_mul_left a hb]
  have hba : b < 2 * a := by
    by_contra hn
    have hle : 2 * a ≤ b := by omega
    nlinarith [Nat.mul_le_mul_left a hle, Nat.mul_le_mul_left b hle]
  refine ⟨ha, hab, hba, ?_⟩
  have h1 : 2 * a - b + b = 2 * a := Nat.sub_add_cancel hba.le
  have h2 : b - a + a = b := Nat.sub_add_cancel hab
  nlinarith

theorem norm_complete (a b : ℕ)
    (h : a ^ 2 + a * b = b ^ 2 + 1) : ∃ n, state n = (a, b) := by
  induction b using Nat.strong_induction_on generalizing a with
  | h b ih =>
      by_cases hb : b = 0
      · subst b
        have ha : a = 1 := by nlinarith
        exact ⟨0, by simp [ha, state]⟩
      · obtain ⟨ha, hab, hba, hn⟩ := norm_descent a b (by omega) h
        obtain ⟨n, he⟩ := ih (b - a) (by omega) (2 * a - b) hn
        refine ⟨n + 1, ?_⟩
        simp only [state, he]
        congr 1 <;> omega

theorem norm_classification (a b : ℕ) :
    a ^ 2 + a * b = b ^ 2 + 1 ↔ ∃! n, state n = (a, b) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := norm_complete a b h
    refine ⟨n, hn, ?_⟩
    intro m hm
    apply second_strictMono.injective
    simp only [hn, hm]
  · rintro ⟨n, hn, _⟩
    simpa only [hn, Prod.fst, Prod.snd] using state_norm n

theorem pell_nat_parity (u v : ℕ) (h : u ^ 2 = 5 * v ^ 2 + 4) : u % 2 = v % 2 := by
  have hm := congrArg (fun z : ℕ => z % 2) h
  have hu := Nat.mod_lt u (by decide : 0 < 2)
  have hv := Nat.mod_lt v (by decide : 0 < 2)
  interval_cases hu' : u % 2 <;> interval_cases hv' : v % 2 <;>
    norm_num [Nat.add_mod, Nat.mul_mod, Nat.pow_mod, hu', hv'] at hm
  all_goals omega

theorem pell_nat_classification (u v : ℕ) :
    u ^ 2 = 5 * v ^ 2 + 4 ↔
      ∃! n, u = 2 * (state n).1 + (state n).2 ∧ v = (state n).2 := by
  constructor
  · intro h
    have huv : v ≤ u := by nlinarith
    have hp := pell_nat_parity u v h
    let a := (u - v) / 2
    have hu : u = 2 * a + v := by dsimp [a]; omega
    have hn : a ^ 2 + a * v = v ^ 2 + 1 := by nlinarith
    obtain ⟨n, hs, _⟩ := (norm_classification a v).mp hn
    refine ⟨n, ?_, ?_⟩
    · simpa only [hs, Prod.fst, Prod.snd] using And.intro hu (rfl : v = v)
    · intro m hm
      apply second_strictMono.injective
      simpa only [hs, Prod.snd] using hm.2.symm
  · rintro ⟨n, ⟨rfl, rfl⟩, _⟩
    have h := state_norm n
    nlinarith

theorem signed_classification (u v : ℤ) :
    u ^ 2 - 5 * v ^ 2 = 4 ↔
      ∃! n, u.natAbs = 2 * (state n).1 + (state n).2 ∧
        v.natAbs = (state n).2 := by
  have he : u ^ 2 - 5 * v ^ 2 = 4 ↔ u.natAbs ^ 2 = 5 * v.natAbs ^ 2 + 4 := by
    have hu : (u.natAbs : ℤ) ^ 2 = u ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
    have hv : (v.natAbs : ℤ) ^ 2 = v ^ 2 := by rw [Int.natCast_natAbs, sq_abs]
    constructor
    · intro h
      have h' : (u.natAbs : ℤ) ^ 2 = 5 * (v.natAbs : ℤ) ^ 2 + 4 := by omega
      exact_mod_cast h'
    · intro h
      have h' : (u.natAbs : ℤ) ^ 2 = 5 * (v.natAbs : ℤ) ^ 2 + 4 := by exact_mod_cast h
      omega
  exact he.trans (pell_nat_classification u.natAbs v.natAbs)

theorem model_pell (n : ℕ) :
    ((2 * (state n).1 + (state n).2 : ℕ) : ℤ) ^ 2 -
      5 * ((state n).2 : ℤ) ^ 2 = 4 := by
  apply (signed_classification _ _).mpr
  refine ⟨n, ⟨rfl, rfl⟩, ?_⟩
  intro m hm
  apply second_strictMono.injective
  simpa using hm.2.symm

theorem first_states : state 0 = (1, 0) ∧ state 1 = (1, 1) ∧
    state 2 = (2, 3) ∧ state 3 = (5, 8) ∧ state 4 = (13, 21) := by decide

end PellFiveFourClassification

theorem solution : ∃ u v : ℤ, u ^ 2 - 5 * v ^ 2 = 4 := by
  exact ⟨3, 1, PellFiveFourClassification.model_pell 1⟩

#print axioms PellFiveFourClassification.state
#print axioms PellFiveFourClassification.state_norm
#print axioms PellFiveFourClassification.first_positive
#print axioms PellFiveFourClassification.second_strictMono
#print axioms PellFiveFourClassification.norm_descent
#print axioms PellFiveFourClassification.norm_complete
#print axioms PellFiveFourClassification.norm_classification
#print axioms PellFiveFourClassification.pell_nat_parity
#print axioms PellFiveFourClassification.pell_nat_classification
#print axioms PellFiveFourClassification.signed_classification
#print axioms PellFiveFourClassification.model_pell
#print axioms PellFiveFourClassification.first_states
#print axioms solution
