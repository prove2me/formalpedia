-- Prove2me | Theorems.Thm_lean_workbook_plus_69953
-- name    : lean_workbook_plus_69953
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/508fbc39-e505-40b9-bb3d-8a35fdc94904
-- statement:
--   From II, we know that the domain is $(-\infty , 5) \cup (5 , \infty)$ . \nFrom III, we know that -4 and 3 are not in the domain either. That limits the domain to \n $(-\infty ,-4) \cup (-4 , 3) \cup (3 , 5) \cup (5 , \infty)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_69953 (∀ x, (x < -4 ∨ -4 < x ∧ x < 3 ∨ 3 < x ∧ x < 5 ∨ 5 < x) ↔ (x < -4 ∨ -4 < x ∨ 3 < x ∨ 5 < x))   :=  by sorry
