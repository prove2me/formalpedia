-- Prove2me | Theorems.Thm_lean_workbook_plus_30969
-- name    : lean_workbook_plus_30969
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/091a8996-e1dd-4f4c-9b22-0f36feed34e0
-- statement:
--   Now we count the number of quadruples modulo $p$ when $p$ is prime. For this we fix any pair $(a,b)$ as long as $(a,b)\ne (0,0)$ . (Since clearly $(a,b)=(0,0)$ cannot lead to a solution of $ad-bc\equiv 1\pmod{p}$ .) This can be done in $p^2-1$ ways. Suppose that $a\ne 0$ (otherwise do the same argument with $b$ ). Pick any $c$ (in $p$ ways). Then $d$ is uniquely determined modulo $p$ as $bc-1$ times the multiplicative inverse of $a$ modulo $p$ . Thus $d$ is uniquely determined in $\{0,1,\ldots,p-1\}$ . In total, $f(p)=p(p^2-1)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30969  (p : ℕ)
  (f : ℕ → ℕ)
  (h₀ : ∀ x, f x = (x^2 - 1)*x)
  (h₁ : Nat.Prime p) :
  f p = p * (p^2 - 1)   :=  by sorry
