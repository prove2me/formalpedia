-- Prove2me | Theorems.Thm_lean_workbook_plus_17693
-- name    : lean_workbook_plus_17693
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/1e8769e6-801c-4b6d-95fc-7759c48ccf2c
-- statement:
--   Let $ f: A \to B$ and let $ C,D$ be two subsets of $ B$ . Are the following true, and under which hp? \n1. $ f^{-1}(C \cap D)=f^{-1}(C) \cap f^{-1}(D)$ \n2. $ f^{-1}(C \cup D)=f^{-1}(C) \cup f^{-1}(D)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17693 (f : A → B) (C D : Set B) : f ⁻¹' (C ∩ D) = f ⁻¹' C ∩ f ⁻¹' D   :=  by sorry
