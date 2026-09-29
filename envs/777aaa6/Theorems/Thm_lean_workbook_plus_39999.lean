-- Prove2me | Theorems.Thm_lean_workbook_plus_39999
-- name    : lean_workbook_plus_39999
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/ff79fca1-ec90-494b-bb99-0ac745884673
-- statement:
--   Now we need to prove divisibility by 5. Looking at quadratic residues mod 5, we see that the square of each prime is congruent to either 1 or 4 mod 5. If they are different, then their sum $ (p^2+q^2)$ is divisible by 5 and we are done. If they are both the same, then their difference $ (p^2 - q^2)$ is divisible by 5. Either way we now have: $ 5 \mid (p^2 + q^2)(p^2 - q^2) = p^4 - q^4$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39999  (p q : ℕ)
  (h₀ : 0 < p ∧ 0 < q)
  (h₁ : p ≠ q)
  (h₂ : 5 ∣ (p^2 + q^2) * (p^2 - q^2)) :
  5 ∣ p^4 - q^4   :=  by sorry
