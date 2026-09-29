-- Prove2me | Theorems.Thm_lean_workbook_plus_32707
-- name    : lean_workbook_plus_32707
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/f0420b35-6485-474e-a4de-4d56a9fcbfa5
-- statement:
--   Let $a,b,c$ be positive. Then $(a^3+2)(b^3+2)(c^3+2)\le (a^3+b^3+c^3+6)^3/27.\ (1)$ We will show that the function $f(a,b,c)=(a^3+b^3+c^3+6)^3-27(872+16abc)\ (2)$ has a maximum of zero under the condition $a^2+b^2+c^2=12. \ (3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_32707 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : (a^3 + 2) * (b^3 + 2) * (c^3 + 2) ≤ (a^3 + b^3 + c^3 + 6)^3 / 27   :=  by sorry
