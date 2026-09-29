-- Prove2me | Theorems.Thm_lean_workbook_plus_57837
-- name    : lean_workbook_plus_57837
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/490adefc-1f7d-4463-a21e-793b9310242d
-- statement:
--   Let $ p<q $ be consecutive prime numbers greater than $ 5 $ . Is it true that $ 2p-q>2 $ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_57837 (p q : ℕ) (hp : 5 < p) (hq : 5 < q) (hpq: p < q) (hpq1: q = p + 1): 2 * p - q > 2   :=  by sorry
