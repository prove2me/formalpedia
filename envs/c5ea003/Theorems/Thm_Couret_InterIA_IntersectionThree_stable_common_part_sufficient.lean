-- Prove2me | Theorems.Thm_Couret_InterIA_IntersectionThree_stable_common_part_sufficient
-- name    : Couret.InterIA.IntersectionThree.stable_common_part_sufficient
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:49:27.978415+00:00
-- url     : https://prove2.me/theorems/17e3ed82-f92e-4e8b-9550-fd4b2f40ce75
-- title:
--   stable common part sufficient
-- statement:
--   Let G be any additive commutative group with decidable equality. For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. For every finite C⊆G and a,h∈G with 2h=0, if z+h∈C for every z∈C, then Q(C∪{a},z)=Q(C∪{a+h},z) for every z∈G. No nonmembership of a in C or nonzero assumption on h is made; C may be empty.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/SingleSwap.lean, lines 72–91; source file SHA-256 e3383e69cd7297f8889be28f527522076c49b30b4ad4047a2c7ec2230a566c63; theorem Couret.InterIA.IntersectionThree.stable_common_part_sufficient

import Definitions.Def_Couret_SingleSwap_148f04e2e72b
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_IntersectionThree_e6b918e458b3

set_option autoImplicit false
namespace Couret.InterIA.IntersectionThree
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem stable_common_part_sufficient (C : Finset G) (a h : G) (hh2 : h+h=0)
    (hstable : ∀ z ∈ C, z+h ∈ C) :
    ∀ z, orderedSquare (insert a C) z = orderedSquare (insert (a+h) C) z := by sorry


end Couret.InterIA.IntersectionThree
