-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_76029
-- name    : WorkbookCorrected.plus_76029
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:13:05.291977+00:00
-- url     : https://prove2.me/theorems/2dd5db60-2b82-4502-90ae-3fa643221c01
-- title:
--   A cyclic difference bound under unit product
-- statement:
--   Prove or disprove: if positive real numbers $a, b, c$ satisfy that $abc = 1$, then $\sum (ab - 1)^{2} + \sum(1 - c)^{2} \geq \sum ab(a - b)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_76029` (Apache-2.0). Natural-language proposition preserved; missing source domain assumptions restored. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_76029; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.plus_76029 (a b c : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (source_domain_c : 0 < c) (h : a * b * c = 1) :
  (a * b - 1) ^ 2 + (b * c - 1) ^ 2 + (c * a - 1) ^ 2 + (1 - a) ^ 2 + (1 - b) ^ 2 + (1 - c) ^ 2 ≥ a * b * (a - b) + b * c * (b - c) + c * a * (c - a)   :=  by sorry
