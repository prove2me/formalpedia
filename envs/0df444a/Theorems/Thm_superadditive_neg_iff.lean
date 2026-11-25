-- Prove2me | Theorems.Thm_superadditive_neg_iff
-- name    : superadditive_neg_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:26:06.156992+00:00
-- url     : https://prove2.me/theorems/cac1c2b0-8a0b-4d22-bebd-f5b7101759bb
-- title:
--   superadditive neg iff: superadditive neg iff
-- statement:
--   The superadditive neg iff construction uses the superadditive neg iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L107-L108
-- source:
--   https://github.com/Egly443/lean-fekete/blob/5faa67a2cbcf0d670bf2b8353336bab5818d6026/Fekete/Superadditive.lean#L107-L108

module
public import Mathlib.Analysis.Subadditive
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Definitions.Def_Fekete_Superadditive
set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open Filter Set
open scoped Topology

theorem superadditive_neg_iff {u : ℕ → ℝ} : (Superadditive fun n ↦ -u n) ↔ Subadditive u := by sorry
