-- Prove2me | Theorems.Thm_sum_card_filter_eq_mul
-- name    : sum_card_filter_eq_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:42:38.430972+00:00
-- url     : https://prove2.me/theorems/433620e5-c757-41d6-8996-b77b6611d091
-- title:
--   sum card filter eq mul: sum card filter eq mul
-- statement:
--   If every element of $M$ matches exactly $c$ vertices under `crit`, then summing the
--   filtered counts over all vertices gives $c$ times the size of $M$.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1642-L1647
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L1642-L1647

module
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Data.Matrix.Mul
public import Definitions.Def_ChipFiringWithLean_Basic
set_option autoImplicit true
@[expose] public section
public section
universe u
open Multiset Finset
attribute [instance] CFGraph.instDecidableEq CFGraph.instFintype CFGraph.instNonempty
open Matrix

theorem sum_card_filter_eq_mul (G : CFGraph) (M : Multiset (G.V × G.V))
    (crit : G.V → G.V × G.V → Prop) [∀ v e, Decidable (crit v e)] (c : ℕ)
    (h_count : ∀ e ∈ M, (Finset.univ.filter (λ v => crit v e)).card = c) :
  ∑ v : G.V, Multiset.card (M.filter (crit v)) = c * Multiset.card M := by sorry
