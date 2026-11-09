-- Prove2me | Theorems.Thm_Couret_InterIA_Fibres_even_four_fibre_ncard
-- name    : Couret.InterIA.Fibres.even_four_fibre_ncard
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:05:51.054681+00:00
-- url     : https://prove2.me/theorems/b5b40fe5-32e6-4971-9f4e-11167c9458e4
-- title:
--   A four-point cyclic square fibre has size one, two, or four
-- statement:
--   For a finite subset $A$ of an abelian group, let $R_A(z)=|\{(a,b)\in A^2:a+b=z\}|$. Let $m>0$. For $S\subseteq\mathbb Z/(2m)\mathbb Z$ with $|S|=4$, let $F=\{T:|T|=4,R_T=R_S\}$. Then
--
--   $$|F|\in\{1,2,4\}.$$
--
--   This is an exhaustive cardinality statement for the full square-profile fibre.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/UniversalFibre.lean, lines 74–88; source file SHA-256 3fd4ea1a66d36d491e106728a1774c805d3d0d2019820d42d877037a669e290b; theorem Couret.InterIA.Fibres.even_four_fibre_ncard

import Definitions.Def_Couret_UniversalFibre_5180566b07f2
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Fibres_antipodal_free_four_ne_half_translate
import Theorems.Thm_Couret_InterIA_Fibres_two_simple_fibre_ncard
import Definitions.Def_Couret_StableFibreLift_7567a251f927

set_option autoImplicit false
namespace Couret.InterIA.Fibres
open Finset Couret.InterIA.Parity Couret.InterIA.Projection

theorem even_four_fibre_ncard (m : ℕ) (hm : 0 < m) (S : Finset (ZMod (2*m))) (hS : S.card=4) :
    (cyclicFourFibre (2*m) S).ncard=1 ∨ (cyclicFourFibre (2*m) S).ncard=2 ∨
      (cyclicFourFibre (2*m) S).ncard=4 := by sorry




end Couret.InterIA.Fibres
