-- Prove2me | Theorems.Thm_lean_workbook_plus_77640
-- name    : lean_workbook_plus_77640
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/0dcfccd5-8438-4ca3-9edb-f00eff03ac01
-- statement:
--   Prove that if $f: A \rightarrow A$ is a surjective map on a finite set $A$, then $f$ is injective.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_77640 (A : Type*) [Finite A] (f : A → A) (hf: Function.Surjective f) : Function.Injective f   :=  by sorry
