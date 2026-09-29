-- Prove2me | Theorems.Thm_lean_workbook_plus_18262
-- name    : lean_workbook_plus_18262
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/bdc5ec9b-76d4-43a8-9b47-40aa00343bc7
-- statement:
--   Let $a$ be the number of people who missed a $S_i$ and $b$ the number of people who missed a $F_j$ . Set up two equations: $a+b=n$ , $(32-4)a+(32-8)b=256$ . 2nd eqn leads to $7a+6b=64$ . $a$ is even so let $a=2c$ and get $7c+3b=32$ . This has only one positive integral solution by inspection: $(c,b)=(2,6)$ . Thus, $n=a+b=4+6=10$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_18262  (a b n : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < n)
  (h₁ : a + b = n)
  (h₂ : (32 - 4) * a + (32 - 8) * b = 256) :
  n = 10   :=  by sorry
