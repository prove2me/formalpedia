-- Prove2me | Theorems.Thm_WorkbookSyntax_plus_44891
-- name    : WorkbookSyntax.plus_44891
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-12T13:00:32.926928+00:00
-- url     : https://prove2.me/theorems/0236f0e8-98b4-4887-9951-ecf3c9707fa7
-- title:
--   Difference between two residue-class sums
-- statement:
--   Among positive integers at most2011, let $A$ be the sum of those congruent to1 modulo3 and $B$ the sum of those congruent to2 modulo3. Then $A-B=1341$.
--
--   Notation repair: Replaced the obsolete finite-sum binder “in” with the current “∈” notation. The ranges, summands, hypotheses and conclusion are unchanged.
--
--   Source: Lean-Workbook record `lean_workbook_plus_44891` (Apache-2.0). [Original declaration](https://prove2.me/theorems/5d82e105-6850-4236-99a2-4c40c8c88b37).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json, record lean_workbook_plus_44891; finite-sum notation repair; Apache-2.0

import Mathlib
open Nat

theorem WorkbookSyntax.plus_44891 (A B : ℕ) (hA : A = ∑ i ∈ Finset.filter (λ x => x % 3 = 1) (Finset.Icc 1 2011), i) (hB : B = ∑ i ∈ Finset.filter (λ x => x % 3 = 2) (Finset.Icc 1 2011), i) : A - B = 1341   :=  by sorry
