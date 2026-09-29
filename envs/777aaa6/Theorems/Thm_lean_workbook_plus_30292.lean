-- Prove2me | Theorems.Thm_lean_workbook_plus_30292
-- name    : lean_workbook_plus_30292
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/53b95d29-8fb2-474b-b2ab-e8d86443ed45
-- statement:
--   Given $a=pq, b=qr, c=rs, d=sp$, prove that $a+b+c+d = (p+r)(q+s)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30292 (a b c d p q r s : ℕ) (hab : a = p * q) (hbc : b = q * r) (hcd : c = r * s) (hda : d = s * p) : a + b + c + d = (p + r) * (q + s)   :=  by sorry
