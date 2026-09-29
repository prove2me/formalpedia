-- Prove2me | Theorems.Thm_lean_workbook_plus_68819
-- name    : lean_workbook_plus_68819
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/5da1eee9-0f14-4282-be9b-2812f3e7b0cf
-- statement:
--   Prove that for every $p>=1$ the Inequality Is true \n\n $2p^3 + 4p + 1 >=6p^2$ \n\n Solution. We manage to show $2p^3 + 4p + 1>6p^2$ for every $p\ge1$ . Put $x=p-1\ge0$ . Then \n\n \begin{align*}2p^3 + 4p + 1-6p^2=2\left(x^3+3x^2+3x+1\right)+4(x+1)+1-6\left(x^2+2x+1\right)=2x^3-2x+1.\end{align*} Consider function $f(x)=2x^3-2x+1$ for $x\ge0$ . Then $f'(x)=2(3x^2-1)$ . Since that $f'(x)>0$ for $x>\frac{1}{\sqrt{3}}$ , and that $f'(x)<0$ for $0\le x<\frac{1}{\sqrt{3}}$ , we conclude that the function $f$ attains its minimum value \n\n $$f\left(\frac{1}{\sqrt{3}}\right)=2\left(\frac{1}{\sqrt{3}}\right)^3-\frac{2}{\sqrt{3}}+1=1-\frac{4\sqrt3}{9}>0,$$ which means $f(x)\ge f\left(\frac{1}{\sqrt{3}}\right)>0$ for any $x\ge0$ . The result follows. $\blacksquare$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_68819  (p : ℝ)
  (h₀ : 1 ≤ p) :
  2 * p^3 + 4 * p + 1 ≥ 6 * p^2   :=  by sorry
