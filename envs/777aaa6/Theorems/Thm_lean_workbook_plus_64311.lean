-- Prove2me | Theorems.Thm_lean_workbook_plus_64311
-- name    : lean_workbook_plus_64311
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/e6e37071-c853-4385-bfc6-3608f77a10f0
-- statement:
--   As in the first solution, we start by considering the expression modulo $7$ . It becomes $x^3 + 2x^2 + 5x+3 \equiv 0 \pmod 7$ . Checking integers $0,1,2,3,4,5,6,7$ , we see that this is only satisfied for $x\equiv 3,4,5 \pmod 7$ . Now, considering the expression modulo $11$ , we get $x^3 + 8x^2 + 2x \equiv 0 \pmod {11}$ . Checking the possible residues, this is satisfied for $x \equiv 0 , 1 , 2 \pmod {11}$ . Finally, modulo $13$ , we get $x^3 + 4 x^2 -11 \equiv 0 \pmod {13}$ , which is satisfied when $x\equiv 2,3,4 \pmod {13}$ . Now, we can check integers $2,3,4 \pmod {13}$ until one works. They are $2,3,4,15,16,17,28,29,30,41,42,43,54,55,56,67$ . Now, $67 \equiv 4 \pmod 7, 67 \equiv 2 \pmod {13}$ , and $67 \equiv 1 \pmod{11}$ . Thus, our answer is $\boxed{67}$ (and you can check to see it works )$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_64311  (x : ℕ)
  (h₀ : 0 < x)
  (h₁ : x^3 + 2 * x^2 + 5 * x + 3 ≡ 0 [ZMOD 7])
  (h₂ : x^3 + 8 * x^2 + 2 * x ≡ 0 [ZMOD 11])
  (h₃ : x^3 + 4 * x^2 - 11 ≡ 0 [ZMOD 13]) :
  67 ≤ x   :=  by sorry
