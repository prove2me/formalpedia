-- Prove2me | Theorems.Thm_lean_workbook_plus_10292
-- name    : lean_workbook_plus_10292
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/ac2b30f0-8230-4f01-bf54-fed84bf98caa
-- statement:
--   Let's denote the sum $ \frac{1}{2}+\frac{1}{4}+\frac{1}{8}+\frac{1}{16}+\frac{1}{32}+...+\frac{1}{2^{n}}$ by $S$ . Then,\n\n$1+\frac{1}{2}+\frac{1}{4}+\frac{1}{8}+\frac{1}{16}+\frac{1}{32}+...+\frac{1}{2^{n-1}} = 2S$ . If you substract, you will get $2S-S=S=1-\frac{1}{2^{n}} $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10292 : ∀ n : ℕ, (∑ k in Finset.range n, (1 / (2^(k + 1)))) = (1 - (1 / 2 ^ n))   :=  by sorry
