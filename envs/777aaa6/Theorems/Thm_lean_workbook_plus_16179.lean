-- Prove2me | Theorems.Thm_lean_workbook_plus_16179
-- name    : lean_workbook_plus_16179
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/df54f5a9-d11c-4539-b549-2daa3b0ddb04
-- statement:
--   Let $ \gcd(b,c) = g \Rightarrow \gcd(a,g) = 1 \Rightarrow au + gv = 1 \Rightarrow au \equiv 1 \bmod g$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16179  (a b c g u v : ℕ)
  (h₀ : Nat.gcd b c = g)
  (h₁ : Nat.gcd a g = 1)
  (h₂ : a * u + g * v = 1)
  (h₃ : 0 < g) :
  a * u ≡ 1 [ZMOD g]   :=  by sorry
