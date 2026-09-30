-- Prove2me | solution 1 for lean_workbook_plus_66739
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:09.973385+00:00
-- url     : https://prove2.me/submissions/e099e661-cfba-4a59-a04b-28c46e5c0f9f

import Mathlib.Analysis.Complex.Basic

theorem solution (n : ℕ) (hn : 0 < n) (A : Finset ℕ) (hA : A.card = n + 1) (hA' : ∀ a ∈ A, 0 < a ∧ a ≤ 2 * n) : ∃ a b, a ∈ A ∧ b ∈ A ∧ a ∣ b := by
  have hne : A.Nonempty := by
    rw [← Finset.card_pos, hA]
    exact Nat.succ_pos n
  obtain ⟨a, haA⟩ := hne
  exact ⟨a, a, haA, haA, dvd_refl a⟩
