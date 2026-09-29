-- Prove2me | Theorems.Thm_lean_workbook_plus_48452
-- name    : lean_workbook_plus_48452
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/3c60569f-d431-4f45-8720-588a9046e2b0
-- statement:
--   By Viete's Theorem again, $pq + qr + rp = 3c$ , $pqr =d$ .\n\n $p+r = 2q \Rightarrow pq + qr = 2q^2 \Rightarrow 3c - rp = 2q^2 \Rightarrow 3qc - pqr = 2q^3$ \n\nThus,\n\n $3bc - d = 2b^3$ \n\n $3bc - 2b^3 = d$ \nFurthermore, $c = \frac{d + 2b^3}{3b}, b \neq 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48452  (b c d : ℂ)
  (h₀ : b ≠ 0)
  (h₁ : 3 * b * c - 2 * b^3 = d) :
  c = (d + 2 * b^3) / (3 * b)   :=  by sorry
