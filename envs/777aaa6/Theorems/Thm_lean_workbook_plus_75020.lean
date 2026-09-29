-- Prove2me | Theorems.Thm_lean_workbook_plus_75020
-- name    : lean_workbook_plus_75020
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/3f728cf2-f74e-46b3-b186-e7065d0d2591
-- statement:
--   Show that the number of handshakes in a group of n people, where each person shakes hands with every other person exactly once, is given by \(\frac{n(n-1)}{2}\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_75020 (n : ℕ) : (n * (n - 1)) / 2 = (n.choose 2)   :=  by sorry
