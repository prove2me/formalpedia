-- Prove2me | solution 1 for lean_workbook_plus_20472
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:15:48.757919+00:00
-- url     : https://prove2.me/submissions/3e94c7d3-ce06-410b-9b7c-1ad7392a703c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

namespace DivisibleQuadraticSequences

def a (n : ℕ) : ℕ := 2 * n + 3

def b (n : ℕ) : ℕ := 2 * n ^ 2 + 8 * n + 7

theorem bounds (n : ℕ) : 1 < a n ∧ a n < b n ∧ b n < (a n) ^ 2 := by
  dsimp [a, b]
  constructor
  · omega
  constructor <;> nlinarith

theorem a_strictMono : StrictMono a := by
  intro m n hmn
  dsimp [a]
  omega

theorem b_strictMono : StrictMono b := by
  intro m n hmn
  have hsq : m ^ 2 < n ^ 2 := (sq_lt_sq₀ (Nat.zero_le m) (Nat.zero_le n)).2 hmn
  dsimp [b]
  omega

theorem predecessor_factor (n : ℕ) : b n - 1 = (a n - 1) * (n + 3) := by
  have ha : a n - 1 = 2 * n + 2 := by dsimp [a]
  have hb : b n - 1 = 2 * n ^ 2 + 8 * n + 6 := by dsimp [b]
  rw [ha, hb]
  ring

theorem successor_factor (n : ℕ) : b n + 1 = (a n + 1) * (n + 2) := by
  dsimp [a, b]
  ring

theorem square_predecessor_factor (n : ℕ) :
    (b n) ^ 2 - 1 = ((a n) ^ 2 - 1) * ((n + 3) * (n + 2)) := by
  have ha : (a n) ^ 2 = (4 * n ^ 2 + 12 * n + 8) + 1 := by
    dsimp [a]
    ring
  have ha' : (a n) ^ 2 - 1 = 4 * n ^ 2 + 12 * n + 8 := by omega
  rw [ha']
  have hb : (b n) ^ 2 =
      (4 * n ^ 2 + 12 * n + 8) * ((n + 3) * (n + 2)) + 1 := by
    dsimp [b]
    ring
  omega

theorem predecessor_dvd (n : ℕ) : (a n - 1) ∣ (b n - 1) :=
  ⟨n + 3, predecessor_factor n⟩

theorem square_predecessor_dvd (n : ℕ) : ((a n) ^ 2 - 1) ∣ ((b n) ^ 2 - 1) :=
  ⟨(n + 3) * (n + 2), square_predecessor_factor n⟩

theorem full_sequence_construction :
    ∃ a b : ℕ → ℕ, StrictMono a ∧ StrictMono b ∧
      (∀ n, 1 < a n ∧ a n < b n ∧ b n < (a n) ^ 2) ∧
      (∀ n, (a n - 1) ∣ (b n - 1)) ∧
      (∀ n, ((a n) ^ 2 - 1) ∣ ((b n) ^ 2 - 1)) :=
  ⟨a, b, a_strictMono, b_strictMono, bounds, predecessor_dvd, square_predecessor_dvd⟩

end DivisibleQuadraticSequences

theorem solution : ∃ a b : ℕ → ℕ,
    (∀ n, 1 < a n ∧ a n < b n ∧ a n ^ 2 < b n ^ 2) ∧
    (∀ n, (a n - 1) ∣ (b n - 1)) ∧
    (∀ n, (a n ^ 2 - 1) ∣ (b n ^ 2 - 1)) := by
  refine ⟨DivisibleQuadraticSequences.a, DivisibleQuadraticSequences.b, ?_,
    DivisibleQuadraticSequences.predecessor_dvd,
    DivisibleQuadraticSequences.square_predecessor_dvd⟩
  intro n
  have h := DivisibleQuadraticSequences.bounds n
  exact ⟨h.1, h.2.1, (sq_lt_sq₀ (Nat.zero_le _) (Nat.zero_le _)).2 h.2.1⟩

#print axioms DivisibleQuadraticSequences.full_sequence_construction
#print axioms DivisibleQuadraticSequences.successor_factor
