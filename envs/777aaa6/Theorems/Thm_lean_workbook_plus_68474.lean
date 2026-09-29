-- Prove2me | Theorems.Thm_lean_workbook_plus_68474
-- name    : lean_workbook_plus_68474
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/0f553068-c3bb-4d7a-95df-8a6df3b756d9
-- statement:
--   Let $u = \sqrt[3]{2 + \sqrt{5}}$ and $v = \sqrt[3]{2 - \sqrt{5}}$. Then $u^3 + v^3 = 4$ and $uv = -1$. Now, let $x = u + v$. Then $x^3 = u^3 + v^3 + 3uv(u + v) = 4 - 3x$. Then $x^3 + 3x - 4 = 0$. By the Rational Root Theorem/inspection, note that $x = 1$ works. Then $(x - 1)(x^2 + x + 4) = 0$. Note that $x^2 + x + 4 = 0$ has no real roots, so $x = \boxed{1}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68474  (u v x : ℝ)
  (h₀ : u = (2 + Real.sqrt 5)^(1 / 3))
  (h₁ : v = (2 - Real.sqrt 5)^(1 / 3))
  (h₂ : x = u + v)
  (h₃ : u^3 + v^3 = 4)
  (h₄ : u * v = -1) :
  x = 1   :=  by sorry
