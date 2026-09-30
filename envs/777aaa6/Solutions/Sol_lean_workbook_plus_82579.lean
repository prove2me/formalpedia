-- Prove2me | solution 1 for lean_workbook_plus_82579
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:24:48.329455+00:00
-- url     : https://prove2.me/submissions/bda01907-b3de-470e-a9b7-0a05eeb58a85

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution (x y z a b c : ℝ) :
    x > 0 ∧ y > 0 ∧ z > 0 ∧ a + b = z ∧ b + c = x ∧ c + a = y →
    a = (y + z - x) / 2 ∧ b = (z + x - y) / 2 ∧ c = (x + y - z) / 2 := by
  rintro ⟨hx, hy, hz, hab, hbc, hca⟩
  exact ⟨by linarith, by linarith, by linarith⟩
