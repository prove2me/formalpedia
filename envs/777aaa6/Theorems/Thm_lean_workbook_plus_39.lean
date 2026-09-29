-- Prove2me | Theorems.Thm_lean_workbook_plus_39
-- name    : lean_workbook_plus_39
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/7c2f9fd9-b41a-45a8-98c9-e4b48f43882d
-- statement:
--   10) We have \(l,a,b,r\) where \(l\) is left, \(a,b\) are the two mirrors and \(r\) is right. If a light particle ends up moving left in \(l\), that means that it hits \(a\), goes \(n\) times up and down between \(a,b\) and goes left afterwards. Here \(n\ge 0\). The probability for this is \(\frac{1}{2}\cdot \left(\frac{1}{4}\right)^n\) .\n\nHence we find \(\frac{1}{2}\sum_{n=0}^\infty \left(\frac{1}{4}\right)^n=\frac{1}{2}\cdot \frac{1}{1-1/4}=\frac{2}{3}\) .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39 :
  ∑' n : ℕ, (1 / 2) * ((1 / 4)^n) = 2 / 3   :=  by sorry
