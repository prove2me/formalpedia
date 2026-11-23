-- Prove2me | Theorems.Thm_outdeg_S_antitone
-- name    : outdeg_S_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T21:42:48.44143+00:00
-- url     : https://prove2.me/theorems/7501ed1a-e300-48a6-8e7e-08f12156cb14
-- title:
--   outdeg S antitone: outdeg S antitone
-- statement:
--   The outdeg S antitone construction uses the outdeg S antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L155-L159
-- source:
--   https://github.com/DhyeyMavani2003/chip-firing-with-lean/blob/b24ecdb21344befdc4f6cb3430fef659eee20066/ChipFiringWithLean/Basic.lean#L155-L159

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

theorem outdeg_S_antitone (G : CFGraph) {S T : Finset G.V} (h : S ⊆ T) (v : G.V) :
    outdeg_S G T v ≤ outdeg_S G S v := by sorry
