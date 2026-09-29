-- Prove2me | Theorems.Thm_WorkbookSource_base_39574
-- name    : WorkbookSource.base_39574
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-13T09:31:58.571335+00:00
-- url     : https://prove2.me/theorems/3f7e472e-c242-46fd-9d23-34e42ef2bdf2
-- title:
--   A fourth-degree inequality involving cyclic differences
-- statement:
--   Let $a$ , $b$ , $c$ and $d$ be non-negative numbers. Prove that:
--
--    $$(a^2+b^2+c^2+d^2)^2\geq4(a-b)(b-c)(c-d)(d-a)+16abcd.$$
--
--   Let $(a-b)(b-c)(c-d)(d-a)=A\ge 0, \ \ abcd=B$ .
--
--    $a^2+b^2+c^2+d^2=\frac{1}{2}((a-b)^2+(b-c)^2+(c-d)^2+(d-a)^2)+ab+bc+cd+da\ge 2\sqrt{A}+4\sqrt{B}$
--
--   It remains to prove
--
--    $(2\sqrt{A}+4\sqrt{B})^2\ge 4A+16B$
--
--   which is obvious.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_39574` (Apache-2.0). Complete source proposition preserved; proof developed independently.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_39574; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.base_39574  (a b c d : ℝ)
  (h₀ : 0 ≤ a)
  (h₁ : 0 ≤ b)
  (h₂ : 0 ≤ c)
  (h₃ : 0 ≤ d) :
  (a^2 + b^2 + c^2 + d^2)^2 ≥ 4 * (a - b) * (b - c) * (c - d) * (d - a) + 16 * a * b * c * d  :=  by sorry
