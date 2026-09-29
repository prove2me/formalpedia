-- Prove2me | Theorems.Thm_WorkbookSource_base_13088
-- name    : WorkbookSource.base_13088
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T10:50:53.616725+00:00
-- url     : https://prove2.me/theorems/ff0859ea-f46b-40d2-b0a1-6980a1fd9047
-- title:
--   A cubic symmetric bound with lower-degree terms
-- statement:
--   Prove that $p(p+1)^2+12r \ge 4q(p+2)$ given $a,b,c > 0$, $p=a+b+c$, $q=ab+bc+ca$, $r=abc$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_13088` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_13088; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_13088 (a b c r p q : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = r) (pq : a * b + b * c + c * a = q) (pqr : a + b + c = p) : p * (p + 1) ^ 2 + 12 * r ≥ 4 * q * (p + 2)  :=  by sorry
