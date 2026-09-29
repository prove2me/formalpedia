-- Prove2me | Theorems.Thm_lean_workbook_plus_4347
-- name    : lean_workbook_plus_4347
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/667f8a94-b1e7-46a9-9fe1-50418d5db85b
-- statement:
--   Let define $f:\mathbb{Z}^{+}\to \mathbb{Z}^{+}$ such that if $p \in \mathbb{P}$ and $p\mid n$ then $v_{p}(f(n)) = 1$ , $f(1) = 1$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4347 (f : ℕ → ℕ) (hf: f 1 = 1) (hf2: ∀ n, (∀ p, p.Prime ∧ p ∣ n → padicValNat p (f n) = 1)) : ∃ n, ∀ p, p.Prime ∧ p ∣ n → padicValNat p (f n) = 1   :=  by sorry
