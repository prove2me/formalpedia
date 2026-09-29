-- Prove2me | Theorems.Thm_lean_workbook_plus_24060
-- name    : lean_workbook_plus_24060
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/13e867f5-5c8b-421b-b7ee-fdbfc739263f
-- statement:
--   Notice that $$-\frac{x^2-3}{x^3+1}\le \frac{(x^2-3)\cos x}{x^3+1}\le \frac{x^2-3}{x^3+1}$$ for all real numbers $x$ because $-1\le \cos x \le 1.$ However, also notice that $$\lim_{x\to \infty}\left(-\frac{x^2-3}{x^3+1}\right)=\lim _{x\to \infty \:}\left(-\frac{\frac{1}{x}-\frac{3}{x^3}}{1+\frac{1}{x^3}}\right)=-\frac{0}{1}=0$$ and similarly $$\lim_{x\to \infty}\left(\frac{x^2-3}{x^3+1}\right)=\lim _{x\to \infty \:}\left(\frac{\frac{1}{x}-\frac{3}{x^3}}{1+\frac{1}{x^3}}\right)=\frac{0}{1}=0.$$ Then, by the Squeeze Theorem, $\lim_{x \to \infty} \dfrac{(x^2-3) \cos x}{x^3+1}=0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24060 : ∀ x : ℝ, -(x^2 - 3) / (x^3 + 1) ≤ (x^2 - 3) * Real.cos x / (x^3 + 1) ∧ (x^2 - 3) * Real.cos x / (x^3 + 1) ≤ (x^2 - 3) / (x^3 + 1)   :=  by sorry
