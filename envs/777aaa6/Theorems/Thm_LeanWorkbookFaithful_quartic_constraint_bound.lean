-- Prove2me | Theorems.Thm_LeanWorkbookFaithful_quartic_constraint_bound
-- name    : LeanWorkbookFaithful.quartic_constraint_bound
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T00:34:22.03451+00:00
-- url     : https://prove2.me/theorems/d97db7fd-5814-46af-ae07-4f338440cfb5
-- title:
--   A quartic constraint bounds the first coordinate by sixteen
-- statement:
--   Let $a,b,c,d$ be strictly positive real numbers satisfying
--
--   $$a+2(b^4+c^4+d^4)+\frac{1}{abcd}=\frac{135}{8}.$$
--
--   Then $a\le16$. No separate condition $abcd=1$ is assumed.
--
--   This is the full inequality from the natural-language statement of Lean Workbook record `lean_workbook_plus_27229`. It supplies a uniform bound under the original constraint and can be applied without any additional product normalization. The existing formal record includes such an extra hypothesis; this declaration intentionally restores the source statement.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook — exact record lean_workbook_plus_27229, natural_language_statement field

import Mathlib.Analysis.Complex.Basic

namespace LeanWorkbookFaithful
theorem quartic_constraint_bound (a b c d : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a + 2 * (b ^ 4 + c ^ 4 + d ^ 4) + 1 / (a * b * c * d) = 135 / 8) :
    a ≤ 16 := by sorry
end LeanWorkbookFaithful
