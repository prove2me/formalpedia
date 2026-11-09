-- Prove2me | Theorems.Thm_Couret_InterIA_IntersectionTwo_pp_actual_square_iff
-- name    : Couret.InterIA.IntersectionTwo.pp_actual_square_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:40:39.357669+00:00
-- url     : https://prove2.me/theorems/01cc35de-62cc-492f-8c52-ccd33a95b245
-- title:
--   pp actual square iff
-- statement:
--   Let G be any additive commutative group with decidable equality. For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. Work in the integer group ring of the stated additive group, with convolution multiplication; write e(a) for the function equal to 1 at a and 0 elsewhere, and I(E)=Σ(a∈E)e(a). For every finite C⊆G, h∈G with h≠0 and 2h=0, and a,b∈G, assume C is disjoint from both {a,a+h} and {b,b+h}. Then Q(C∪{a,a+h},z)=Q(C∪{b,b+h},z) for every z∈G if and only if (1+e(h))(e(a)−e(b))(I(C)+e(a)+e(b))=0. Here 1=e(0); C may be empty and a=b is allowed.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/IntersectionTwoAlgebra.lean, lines 128–136; source file SHA-256 d3f401d66028b6fe548ef50d997edcce7176b82bbf76716b11c088a8ea729af9; theorem Couret.InterIA.IntersectionTwo.pp_actual_square_iff

import Definitions.Def_Couret_IntersectionTwoAlgebra_ba9c300e13f5
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
import Theorems.Thm_Couret_InterIA_IntersectionTwo_pp_square_iff
import Definitions.Def_Couret_SingleSwap_148f04e2e72b

set_option autoImplicit false
namespace Couret.InterIA.IntersectionTwo
open Finset Couret.InterIA.Parity Couret.InterIA.GroupRing
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem pp_actual_square_iff (C : Finset G) (h : G) (hh : h ≠ 0) (hh2 : h+h=0)
    (a b : G) (ha : Disjoint C (Couret.InterIA.Fibres.fibre h a))
    (hb : Disjoint C (Couret.InterIA.Fibres.fibre h b)) :
    (∀ z, orderedSquare (C ∪ Couret.InterIA.Fibres.fibre h a) z =
      orderedSquare (C ∪ Couret.InterIA.Fibres.fibre h b) z) ↔
      (1+atom h)*(atom a-atom b)*(indicator C+atom a+atom b)=0 := by sorry


end Couret.InterIA.IntersectionTwo
