-- Prove2me | Theorems.Thm_lean_workbook_plus_48954
-- name    : lean_workbook_plus_48954
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/7f3cc582-7dcb-4a88-a025-d453a7c81b7a
-- statement:
--   Let $\sin x_i=\sqrt{\frac{a_i}{10}}$ , where $a_i\geq0$ . Hence, $\sum_{i=1}^{10}a_i=10$ and $\sum_{i=1}^{10}\left(\cos x_i-3\sin x_i\right)\geq0\Leftrightarrow$ \n\n $\Leftrightarrow\sum_{i=1}^{10}\left(\sqrt{10-a_i}-3\sqrt{a_i}\right)\geq0\Leftrightarrow\sum_{i=1}^{10}\left(\frac{1-a_i}{\sqrt{10-a_i}+3\sqrt{a_i}}+\frac{a_i-1}{6}\right)\geq0\Leftrightarrow$ \n\n $\Leftrightarrow\sum_{i=1}^{10}\frac{(a_i-1)\left(\sqrt{10-a_i}+3\sqrt{a_i}-6\right)}{\sqrt{10-a_i}+3\sqrt{a_i}}\geq0\Leftrightarrow$ \n\n $\Leftrightarrow\sum_{i=1}^{10}\frac{(a_i-1)^2\left(\frac{3}{\sqrt{a_i}+1}-\frac{1}{3+\sqrt{10-a_i}}\right)}{\sqrt{10-a_i}+3\sqrt{a_i}}\geq0$ , which is obvious.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48954  (a : ℕ → NNReal)
  (h₀ : ∑ x in Finset.range 10, a x = 10)
  (h₁ : 0 ≤ ∑ x in Finset.range 10, (Real.cos (Real.arcsin (Real.sqrt (a x / 10))) - 3 * Real.sin (Real.arcsin (Real.sqrt (a x / 10))))) :
  ∑ x in Finset.range 10, (Real.cos (Real.arcsin (Real.sqrt (a x / 10))) - 3 * Real.sin (Real.arcsin (Real.sqrt (a x / 10)))) ≥ 0   :=  by sorry
