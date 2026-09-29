-- Prove2me | Theorems.Thm_lean_workbook_plus_50103
-- name    : lean_workbook_plus_50103
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/0f6097ae-f715-43cc-ac09-ac42b8623a24
-- statement:
--   Given that $123^{1000}\equiv 1\pmod{10000}$ . We are asked to determine $123^{9999}\pmod{10000}$ . This is basically finding its inverse mod. To elaborate, set $123^{9999}\equiv x\pmod{10000}$ . Then, $123^{1000}\equiv 123x\equiv 1\pmod{10000}$. To compute this $x$ is finding the inverse of $123$ modulo $10000$ . To do this, one could simply use the as stated by Derive_Foiler by converting our given congruence in the form of a linear diophantine equation which would look like this: $123x-10000y=1$. Since $\gcd(123,10000)=1$ we can compute integer solutions for $x$ . Hence, the last four digits of $x$ are $\boxed{9187}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50103  (x : ℕ)
  (h₀ : 0 < x)
  (h₁ : x < 10000)
  (h₂ : (123^1000 % 10000) = 1)
  (h₃ : (123^9999 % 10000) = x) :
  x = 9187   :=  by sorry
