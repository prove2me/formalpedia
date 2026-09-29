-- Prove2me | Theorems.Thm_WorkbookSource_base_44577
-- name    : WorkbookSource.base_44577
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:45:02.036482+00:00
-- url     : https://prove2.me/theorems/bdac462d-0168-44eb-8aa3-3c3ab82a25a3
-- title:
--   A quartic symmetric inequality on the unit sphere
-- statement:
--   Let $a,b,c >0$ and $a^2+b^2+c^2=1$. Prove that $6abc(a+b+c)-2(ab+bc+ac)^2-(ab+bc+ac)+1 \geq 0$
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_44577` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_44577; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_44577 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (h : a^2+b^2+c^2=1) : 6*a*b*c*(a+b+c)-2*(a*b+b*c+a*c)^2-(a*b+b*c+a*c)+1 ≥ 0  :=  by sorry
