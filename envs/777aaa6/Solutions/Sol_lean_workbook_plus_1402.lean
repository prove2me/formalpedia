-- Prove2me | solution 1 for lean_workbook_plus_1402
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:23:54.574563+00:00
-- url     : https://prove2.me/submissions/f0e52b09-d31f-4feb-99ed-22d8e76bc43a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (ha : 1 ≤ a ∧ a ≤ 2) (hb : 1 ≤ b ∧ b ≤ 2) (hc : 1 ≤ c ∧ c ≤ 2) : 2 * (a * b + b * c + c * a) ≥ a ^ 2 + b ^ 2 + c ^ 2 + a + b + c := by
  (intros; nlinarith)
