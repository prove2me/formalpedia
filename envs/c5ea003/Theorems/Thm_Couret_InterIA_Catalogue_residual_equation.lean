-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_residual_equation
-- name    : Couret.InterIA.Catalogue.residual_equation
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:44:25.046541+00:00
-- url     : https://prove2.me/theorems/583fa7b3-7ae7-40e9-8b38-163e6e2cc83c
-- title:
--   residual equation
-- statement:
--   For a finite set E, write Q(E,z) for the number of ordered pairs (a,b) in E × E with a+b=z. Work in the integer group ring of the stated additive group, with convolution multiplication; write e(a) for the function equal to 1 at a and 0 elsewhere, and I(E)=Σ(a∈E)e(a). For every positive natural m, finite C⊆ℤ/(2m)ℤ and a,b∈ℤ/(2m)ℤ, assume C is disjoint from {a,a+m} and from {b,b+m}, and Q(C∪{a,a+m},z)=Q(C∪{b,b+m},z) for every z∈ℤ/(2m)ℤ. Let π be reduction modulo m and P=Σ(c∈C)e(π(c)) in the integer group ring of ℤ/mℤ, retaining multiplicities of projected points. Then (e(π(a))−e(π(b)))(P+e(π(a))+e(π(b)))=0. The finite set C may be empty and a,b need not be distinct.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/QuotientResidual.lean, lines 17–37; source file SHA-256 29c3ae2cbecdf646a84bc5ab6931803cdc7db5ad9705778c5cd73f60b149f4bb; theorem Couret.InterIA.Catalogue.residual_equation

import Definitions.Def_Couret_QuotientResidual_b532f552ee0f
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_IntersectionTwo_pp_actual_square_iff
import Definitions.Def_Couret_L4Assembly_154a326d9c14

set_option autoImplicit false
namespace Couret.InterIA.Catalogue
open Finset Couret.InterIA.Parity Couret.InterIA.Fibres Couret.InterIA.GroupRing
open Couret.InterIA.Projection

theorem residual_equation (m : ℕ) (hm : 0 < m) (C : Finset (ZMod (2*m)))
    (a b : ZMod (2*m))
    (ha : Disjoint C (fibre (m : ZMod (2*m)) a))
    (hb : Disjoint C (fibre (m : ZMod (2*m)) b))
    (hsq : ∀ z, orderedSquare (C ∪ fibre (m : ZMod (2*m)) a) z=
      orderedSquare (C ∪ fibre (m : ZMod (2*m)) b) z) :
    (A (projection m a)-A (projection m b))*residual m C a b=0 := by sorry














end Couret.InterIA.Catalogue
