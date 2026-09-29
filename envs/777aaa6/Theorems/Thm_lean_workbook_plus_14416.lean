-- Prove2me | Theorems.Thm_lean_workbook_plus_14416
-- name    : lean_workbook_plus_14416
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/03f733f9-5aa7-4c17-91c9-e9678ea3c7b1
-- statement:
--   A function $s: A \to B$ is called a surjective function if $\forall b \in B$, exists $a \in A$ such that $b=s(a)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14416 {A B : Type} (s : A → B) : (∀ b : B, ∃ a : A, b = s a) ↔ Function.Surjective s   :=  by sorry
