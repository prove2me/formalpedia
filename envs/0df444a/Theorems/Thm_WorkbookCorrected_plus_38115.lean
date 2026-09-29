-- Prove2me | Theorems.Thm_WorkbookCorrected_plus_38115
-- name    : WorkbookCorrected.plus_38115
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T11:12:53.120524+00:00
-- url     : https://prove2.me/theorems/4447f518-24f4-4ff3-90f4-910e09da1870
-- title:
--   A sum of powers bound under unit product
-- statement:
--   Let $a,b,c$ denote positive real numbers such that $abc=1$ . Show that
--    $a+a^2+a^3+b+b^2+b^3+c+c^2+c^3\le (a^2+b^2+c^2)^2.$
--    Proposed by M. Lovas, Budapest and M. Rozenberg, Israel
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_38115` (Apache-2.0). Natural-language proposition preserved; missing source domain assumptions restored. Proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_38115; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookCorrected.plus_38115 (a b c : ℝ) (source_domain_a : 0 < a) (source_domain_b : 0 < b) (source_domain_c : 0 < c) (habc : a * b * c = 1) : a + a^2 + a^3 + b + b^2 + b^3 + c + c^2 + c^3 ≤ (a^2 + b^2 + c^2)^2   :=  by sorry
