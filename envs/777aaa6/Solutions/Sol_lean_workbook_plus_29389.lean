-- Prove2me | solution 1 for lean_workbook_plus_29389
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:15:38.250165+00:00
-- url     : https://prove2.me/submissions/fbad8528-687e-445c-b7c5-c2cb44405d2f

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

namespace MutualQuadraticDivisibility

def pair (m : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, m + 1)
  | n + 1 => ((pair m n).2, (m + 2) * (pair m n).2 - (pair m n).1)

theorem step_properties (m a b : ℕ) (hab : a < b)
    (hinv : a ^ 2 + b ^ 2 + m = (m + 2) * a * b) :
    let c := (m + 2) * b - a
    b < c ∧ a * c = b ^ 2 + m ∧ b ^ 2 + c ^ 2 + m = (m + 2) * b * c := by
  let c := (m + 2) * b - a
  change b < c ∧ a * c = b ^ 2 + m ∧ b ^ 2 + c ^ 2 + m = (m + 2) * b * c
  have hscaled : 2 * b ≤ (m + 2) * b := Nat.mul_le_mul_right b (by omega)
  have hle : a ≤ (m + 2) * b := by omega
  have hrestore : c + a = (m + 2) * b := Nat.sub_add_cancel hle
  have hinc : b < c := by omega
  have hfactor : a * c = b ^ 2 + m := by
    nlinarith [congrArg (fun t : ℕ => a * t) hrestore]
  refine ⟨hinc, hfactor, ?_⟩
  nlinarith [congrArg (fun t : ℕ => c * t) hrestore]

theorem pair_properties (m : ℕ) (hm : 0 < m) (n : ℕ) :
    0 < (pair m n).1 ∧ (pair m n).1 < (pair m n).2 ∧
      (pair m n).1 ^ 2 + (pair m n).2 ^ 2 + m =
        (m + 2) * (pair m n).1 * (pair m n).2 := by
  induction n with
  | zero =>
      change 0 < 1 ∧ 1 < m + 1 ∧ 1 ^ 2 + (m + 1) ^ 2 + m = (m + 2) * 1 * (m + 1)
      refine ⟨by omega, by omega, ?_⟩
      ring
  | succ n ih =>
      rcases ih with ⟨ha, hab, hinv⟩
      have hs := step_properties m (pair m n).1 (pair m n).2 hab hinv
      change 0 < (pair m n).2 ∧
        (pair m n).2 < (m + 2) * (pair m n).2 - (pair m n).1 ∧ _
      exact ⟨lt_trans ha hab, hs.1, hs.2.2⟩

theorem divisibility_of_invariant (m a b : ℕ)
    (hinv : a ^ 2 + b ^ 2 + m = (m + 2) * a * b) :
    a ∣ b ^ 2 + m ∧ b ∣ a ^ 2 + m := by
  constructor
  · apply (Nat.dvd_add_right (show a ∣ a ^ 2 from ⟨a, by ring⟩)).mp
    refine ⟨(m + 2) * b, ?_⟩
    nlinarith [hinv]
  · apply (Nat.dvd_add_right (show b ∣ b ^ 2 from ⟨b, by ring⟩)).mp
    refine ⟨(m + 2) * a, ?_⟩
    nlinarith [hinv]

theorem first_strictMono (m : ℕ) (hm : 0 < m) :
    StrictMono (fun n => (pair m n).1) := by
  apply strictMono_nat_of_lt_succ
  intro n
  change (pair m n).1 < (pair m n).2
  exact (pair_properties m hm n).2.1

theorem infinite_pairs (m : ℕ) (hm : 0 < m) :
    {p : ℕ × ℕ | 0 < p.1 ∧ 0 < p.2 ∧ p.1 ∣ p.2 ^ 2 + m ∧
      p.2 ∣ p.1 ^ 2 + m}.Infinite := by
  have hinj : Function.Injective (pair m) := by
    intro i j hij
    apply (first_strictMono m hm).injective
    exact congrArg Prod.fst hij
  have hrange : (Set.range (pair m)).Infinite := Set.infinite_range_of_injective hinj
  apply hrange.mono
  rintro p ⟨n, rfl⟩
  rcases pair_properties m hm n with ⟨ha, hab, hinv⟩
  exact ⟨ha, lt_trans ha hab, divisibility_of_invariant m _ _ hinv⟩

end MutualQuadraticDivisibility

theorem solution (m : ℕ) (hm : 0 < m) :
    ∃ a b : ℕ, a ∣ b ^ 2 + m ∧ b ∣ a ^ 2 + m := by
  obtain ⟨⟨a, b⟩, _, _, hab, hba⟩ :=
    (MutualQuadraticDivisibility.infinite_pairs m hm).nonempty
  exact ⟨a, b, hab, hba⟩
