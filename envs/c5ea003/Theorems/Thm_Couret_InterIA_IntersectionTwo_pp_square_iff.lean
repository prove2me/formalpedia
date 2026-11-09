-- Prove2me | Theorems.Thm_Couret_InterIA_IntersectionTwo_pp_square_iff
-- name    : Couret.InterIA.IntersectionTwo.pp_square_iff
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:33:16.108766+00:00
-- url     : https://prove2.me/theorems/d806b0ae-b1ab-4ef8-a2eb-f7eaf30cd382
-- title:
--   pp square iff
-- statement:
--   For every abelian group $G$ with decidable equality, for every $h∈G$ with $2h=0$, every $c∈ℤ[G]$, and every $a,b∈G$, write $e_x$ for the group-ring element with coefficient $1$ at $x$ and zero elsewhere. Then $(c+(1+e_h)e_a)^2=(c+(1+e_h)e_b)^2$ if and only if $(1+e_h)(e_a-e_b)(c+e_a+e_b)=0$. The value $h=0$ and equal $a,b$ are allowed; $1=e_0$.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/IntersectionTwoAlgebra.lean, lines 100–118; source file SHA-256 d3f401d66028b6fe548ef50d997edcce7176b82bbf76716b11c088a8ea729af9; theorem Couret.InterIA.IntersectionTwo.pp_square_iff

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
import Theorems.Thm_Couret_InterIA_L4_normal_form_identity
import Definitions.Def_Couret_SingleSwap_148f04e2e72b

set_option autoImplicit false
namespace Couret.InterIA.IntersectionTwo
open Finset Couret.InterIA.Parity Couret.InterIA.GroupRing
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem pp_square_iff (h : G) (hh2 : h+h=0) (c : AddMonoidAlgebra ℤ G) (a b : G) :
    (c+(1+atom h)*atom a)^2 = (c+(1+atom h)*atom b)^2 ↔
      (1+atom h)*(atom a-atom b)*(c+atom a+atom b)=0 := by sorry






end Couret.InterIA.IntersectionTwo
