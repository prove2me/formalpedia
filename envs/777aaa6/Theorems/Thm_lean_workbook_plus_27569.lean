-- Prove2me | Theorems.Thm_lean_workbook_plus_27569
-- name    : lean_workbook_plus_27569
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/8a79d706-414f-4bda-be53-eb304ac1ab9a
-- statement:
--   Explain why the sets $M_d = \{x \in G : |x| = d\}$ are disjoint for different divisors $d$ of $n$, where $G$ is a group and $|x|$ denotes the order of element $x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27569 (G : Type*) [Group G] (n : ℕ) (M : ℕ → Set G) (hM : ∀ d : ℕ, M d = {x : G | orderOf x = d}) : ∀ d1 d2 : ℕ, d1 ≠ d2 → M d1 ∩ M d2 = ∅   :=  by sorry
