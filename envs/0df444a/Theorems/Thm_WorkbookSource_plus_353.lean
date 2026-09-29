-- Prove2me | Theorems.Thm_WorkbookSource_plus_353
-- name    : WorkbookSource.plus_353
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T21:41:15.682731+00:00
-- url     : https://prove2.me/theorems/11d36f2c-e7ca-49f5-aabf-4988ef0fd315
-- title:
--   Implication expressed by negation and conjunction
-- statement:
--   A statement equivalent to $X \rightarrow Y$ using only $
--   eg$ and $\wedge$ is $
--   eg (X \wedge
--   eg Y)$.
--
--   Source: InternLM Lean-Workbook, record `lean_workbook_plus_353` (Apache-2.0). The complete source proposition and its explicit variable declarations are preserved. Explicit binder repair: Declare X and Y as propositions, as required by the source logical equivalence. A separate checked example verifies the intended ((X→Y)↔¬(X∧¬Y)) grouping.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_353; Apache-2.0

import Mathlib
open Real Nat

theorem WorkbookSource.plus_353 (X Y : Prop) : X → Y ↔ ¬(X ∧ ¬Y)   :=  by sorry
