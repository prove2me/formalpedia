-- Prove2me | Theorems.Thm_lean_workbook_plus_8357
-- name    : lean_workbook_plus_8357
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/8db7638b-dfb6-48a4-ba17-a724ab4944e2
-- statement:
--   Prove the theorem that states: Let $E$ be a set, $g \colon E \to E$ , and $a \in E$ . There is a unique application $f\colon \mathbb{N} \to E$ such that $f(0) = a$ and $f(n+1) = g(f(n))$ for every natural number $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8357 (E : Type) (g : E → E) (a : E) : ∃! f : ℕ → E, f 0 = a ∧ ∀ n, f (n + 1) = g (f n)   :=  by sorry
