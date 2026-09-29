-- Prove2me | Theorems.Thm_lean_workbook_plus_9027
-- name    : lean_workbook_plus_9027
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/a303ff83-4c30-4572-a20a-29e5b65f9733
-- statement:
--   If $f(-1)=p,f(0)=q,f(1)=r$ then $a={{p+r-2q}\over 2},b={{r-p}\over 2},c=q$ and $6|a|+|b|+9|c|=3|p+r-2q|+{1\over 2}|p-r|+9|q|=:\alpha$ where $p,q,r\in [-1,1]$ . Note that we may assume $q\ge {{p+r}\over 2}$ , replacing $f$ by $-f$ if necessary and also that $p\le r$ , replacing $f(x)$ by $f(-x)$ , if necessary. Hence $p\le r, {{p+r}\over 2}\le q$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9027  (p q r a b c α : ℝ)
  (f : ℝ → ℝ)
  (h₀ : ∀ x, f x ∈ Set.Icc (-1) 1)
  (h₁ : f (-1) = p)
  (h₂ : f 0 = q)
  (h₃ : f 1 = r)
  (h₄ : a = (p + r - 2 * q) / 2)
  (h₅ : b = (r - p) / 2)
  (h₆ : c = q)
  (h₇ : 6 * abs a + abs b + 9 * abs c = α) :
  3 * abs (p + r - 2 * q) + 1 / 2 * abs (r - p) + 9 * abs q = α   :=  by sorry
