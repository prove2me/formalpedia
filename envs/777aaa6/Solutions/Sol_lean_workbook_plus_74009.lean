-- Prove2me | solution 1 for lean_workbook_plus_74009
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:39:23.436263+00:00
-- url     : https://prove2.me/submissions/cc98f64c-b626-4d02-97a5-d03d763a3d94

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring

theorem solution {m : ℕ} (hm : 0 < m)
    (h5 : ∀ a : ℕ, 0 < a → a^4 ∣ m → a ∣ m) :
    ∀ a : ℕ, 0 < a → a^5 ∣ m → a ∣ m := by
  intro a ha hdiv
  have h45 : a^4 ∣ a^5 := ⟨a, by ring⟩
  exact h5 a ha (dvd_trans h45 hdiv)
