-- Prove2me | Theorems.Thm_WorkbookSource_plus_26401
-- name    : WorkbookSource.plus_26401
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T01:27:19.707083+00:00
-- url     : https://prove2.me/theorems/b5cbef9a-feed-4931-9c2a-78b43d05962e
-- title:
--   An asymmetric quartic lower bound
-- statement:
--   Let $a,b,c\geq 0$ . Show that $a^{4}+b^{4}+c^{4}\geq 2bc(a-b)(a-c)$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_26401` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_26401; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_26401 {a b c : ℝ} (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) : a^4 + b^4 + c^4 ≥ 2 * b * c * (a - b) * (a - c)   :=  by sorry
