-- Prove2me | solution 1 for SudokuBridge.isSudokuSolution_sudokuColor
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T13:12:40.669594+00:00
-- url     : https://prove2.me/submissions/0109ca0a-3ebc-43c4-9572-a64104953ae0

import Mathlib
import Definitions.Def_Bridges_SudokuChromatic
open SudokuBridge in
theorem solution {n : ℕ} (hn : 0 < n) :
    IsSudokuSolution n (sudokuColor n hn) := by
  -- two-digit base-`n` numbers: uniqueness and the bound `n·a + b < n²`
  have hdig : ∀ a b a' b' : ℕ, b < n → b' < n → n * a + b = n * a' + b' → a = a' ∧ b = b' := by
    intro a b a' b' hb hb' h
    have h1 := congrArg (· / n) h
    have h2 := congrArg (· % n) h
    simp only [Nat.mul_add_div hn, Nat.div_eq_of_lt hb, Nat.div_eq_of_lt hb', Nat.mul_add_mod,
      Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hb', add_zero] at h1 h2
    exact ⟨h1, h2⟩
  have hlt : ∀ a b : ℕ, a < n → b < n → n * a + b < n * n := by
    intro a b ha hb
    calc n * a + b < n * a + n := by omega
      _ = n * (a + 1) := by ring
      _ ≤ n * n := Nat.mul_le_mul_left n ha
  have hdivlt : ∀ r : Fin (n * n), (r : ℕ) / n < n := fun r =>
    Nat.div_lt_of_lt_mul r.isLt
  have hrec : ∀ r : ℕ, n * (r / n) + r % n = r := fun r => Nat.div_add_mod r n
  refine ⟨?_, ?_, ?_⟩
  · -- rows: same `r`, the value is `(A + c) mod n²`
    rintro ⟨r, c⟩ ⟨r', c'⟩ hrow hne heq
    simp only [sameRow] at hrow
    subst hrow
    have h : n * ((r : ℕ) % n) + (r : ℕ) / n + c ≡ n * ((r : ℕ) % n) + (r : ℕ) / n + c'
        [MOD n * n] := congrArg Fin.val heq
    have := Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_left_cancel' _ h) c.isLt c'.isLt
    exact hne (Prod.ext rfl (Fin.ext this))
  · -- columns: `r ↦ n·(r mod n) + r div n` swaps the two base-`n` digits
    rintro ⟨r, c⟩ ⟨r', c'⟩ hcol hne heq
    simp only [sameCol] at hcol
    subst hcol
    have h : n * ((r : ℕ) % n) + (r : ℕ) / n + c ≡ n * ((r' : ℕ) % n) + (r' : ℕ) / n + c
        [MOD n * n] := congrArg Fin.val heq
    have h' := Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' _ h)
      (hlt _ _ (Nat.mod_lt _ hn) (hdivlt r)) (hlt _ _ (Nat.mod_lt _ hn) (hdivlt r'))
    obtain ⟨h1, h2⟩ := hdig _ _ _ _ (hdivlt r) (hdivlt r') h'
    have : (r : ℕ) = r' := by rw [← hrec r, ← hrec r', h1, h2]
    exact hne (Prod.ext (Fin.ext this) rfl)
  · -- boxes: same block row `q` and block column `b`
    rintro ⟨r, c⟩ ⟨r', c'⟩ ⟨hq, hb⟩ hne heq
    simp only at hq hb
    have h : n * ((r : ℕ) % n) + (r : ℕ) / n + c ≡ n * ((r' : ℕ) % n) + (r' : ℕ) / n + c'
        [MOD n * n] := congrArg Fin.val heq
    have e1 : n * ((r : ℕ) % n) + (r : ℕ) / n + c
        = (n * ((r : ℕ) % n) + (c : ℕ) % n) + ((r : ℕ) / n + n * ((c : ℕ) / n)) := by
      have := hrec c
      linarith
    have e2 : n * ((r' : ℕ) % n) + (r' : ℕ) / n + c'
        = (n * ((r' : ℕ) % n) + (c' : ℕ) % n) + ((r : ℕ) / n + n * ((c : ℕ) / n)) := by
      have := hrec c'
      rw [hq, hb]
      linarith
    rw [e1, e2] at h
    have h' := Nat.ModEq.eq_of_lt_of_lt (Nat.ModEq.add_right_cancel' _ h)
      (hlt _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn)) (hlt _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn))
    obtain ⟨h1, h2⟩ := hdig _ _ _ _ (Nat.mod_lt _ hn) (Nat.mod_lt _ hn) h'
    have hr : (r : ℕ) = r' := by rw [← hrec r, ← hrec r', h1, hq]
    have hc : (c : ℕ) = c' := by rw [← hrec c, ← hrec c', h2, hb]
    exact hne (Prod.ext (Fin.ext hr) (Fin.ext hc))
