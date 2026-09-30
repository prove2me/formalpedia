-- Prove2me | solution 1 for lean_workbook_plus_51149
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:38:31.715549+00:00
-- url     : https://prove2.me/submissions/7cbf576e-a3e8-4373-9cd5-a91982a085b7

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (n k : ℕ) (h₁ : k ^ 2 ≤ n) (h₂ : n < (k + 1) ^ 2) :
    ∃ r : ℕ, n = k ^ 2 + r ∧ r < 2 * k + 1 := by
  have hsq : (k + 1) ^ 2 = k ^ 2 + (2 * k + 1) := by ring
  rw [hsq] at h₂
  refine ⟨n - k ^ 2, ?_, ?_⟩ <;> omega

#print axioms solution
