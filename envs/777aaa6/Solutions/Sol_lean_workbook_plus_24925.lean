-- Prove2me | solution 1 for lean_workbook_plus_24925
-- status  : ACCEPTED   (disprove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:25.574432+00:00
-- url     : https://prove2.me/submissions/36109dbe-e1d1-4b2d-bdd5-169248ee498a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.GCD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Lean.Elab.Tactic.Grind
import Mathlib.Tactic.Positivity
import Lean
import Mathlib.Analysis.Complex.Basic
set_option autoImplicit false
theorem solution : ¬ (∀ (n : ℕ)
  (f : ℕ → ℕ)
  (h₀ : ∃ n, f n ≠ n)
  (h₁ : ∀ n, f (f n) = n * f 1)
  (h₂ : ∃ n, f n ≠ n * f 1), f 1 = 1 ∧ ∀ n, f n = n) := by
  intro h
  let f : ℕ → ℕ := fun n => if n = 0 then 2 else if n = 2 then 0 else n
  have hf : f 1 = 1 := by norm_num [f]
  have hi (n : ℕ) : f (f n) = n * f 1 := by
    by_cases h0 : n = 0
    · subst n; norm_num [f]
    · by_cases h2 : n = 2
      · subst n; norm_num [f]
      · simp [f, h0, h2]
  have hc := h 0 f ⟨0, by norm_num [f]⟩ hi ⟨0, by norm_num [f]⟩
  have hc0 := hc.2 0
  norm_num [f] at hc0
