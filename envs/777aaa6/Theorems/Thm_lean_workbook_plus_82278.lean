-- Prove2me | Theorems.Thm_lean_workbook_plus_82278
-- name    : lean_workbook_plus_82278
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.420916+00:00
-- url     : https://prove2.me/theorems/6c21d33f-46ed-4812-95d0-0c33ff308944
-- statement:
--   Let $f:\mathbb{N} \cup \{0\} \to \mathbb{N} \cup \{0\}$ be defined by $f(0)=0$ ,\n $$f(2n+1)=2f(n)$$ for $n \ge 0$ and \n $$f(2n)=2f(n)+1$$ for $n \ge 1$ \n\n If $g(n)=f(f(n))$ , prove that $g(n-g(n))=0$ for all $n \ge 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_82278 (f g : ℕ → ℕ) (hf: f 0 = 0 ∧ ∀ n, f (2 * n + 1) = 2 * f n ∧ f (2 * n) = 2 * f n + 1) (hg: ∀ n, g n = f (f n)): ∀ n, g (n - g n) = 0   :=  by sorry
