-- Prove2me | Theorems.Thm_lean_workbook_plus_65318
-- name    : lean_workbook_plus_65318
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/469aeb94-a570-4b3d-baa4-22d184fc382e
-- statement:
--   Unfortunately, such a sequence cannot exist! Define $f(x) = \sqrt{x - \dfrac {1} {x}}$ for $x\geq 1$ . It is easily seen that $f(x) < x$ and $a_{n+1} = f(a_n)$ .\n\nIf such a sequence existed, then it would be decreasing and lower bounded by $0$ , so there will exist $a = \lim_{n\to \infty} = \inf a_n \geq 0$ .\n\nBut then $a$ would be a root for $x^3-x^2+1=0$ , which only has one negative real root, contradiction.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65318  (a : ℕ → NNReal)
  (h₀ : 0 < a 0)
  (h₁ : ∀ n, a (n + 1) = Real.sqrt (a n - 1 / a n)) :
  False   :=  by sorry
