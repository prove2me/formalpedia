-- Prove2me | Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_gcd_support_reduction
-- name    : Couret.InterIA.Catalogue.Quarter.Primitive.gcd_support_reduction
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:13:51.91121+00:00
-- url     : https://prove2.me/theorems/a42c541b-8b92-4664-b751-69a485c8d3f2
-- title:
--   gcd support reduction
-- statement:
--   In ℤ/(4q)ℤ put A={0,q,x,x+2q}, B={0,q,x+q,x+3q}, and D={0,q,2q,3q}; these are sets, so repeated entries count once. Here affine equivalence of E and F means that F={u z+v : z∈E} for some unit u of the ambient residue ring and some element v. For every positive natural q and x∈ℤ/(4q)ℤ with x∉D and A,B not affinely equivalent, there exist naturals d,b,a such that d>0, b>0, q=db, val(x)=da, gcd(a,b)=1, b has remainder 2 modulo 4, and the residue of a modulo 4b is a unit. Moreover, the images of {0,b,a,a+2b} and {0,b,a+b,a+3b}, interpreted as finite subsets of ℤ/(4b)ℤ, under w↦d·val(w) modulo 4q are respectively A and B. Here val denotes the least nonnegative representative in its source ring.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-hk-review-corollaries-20261103/QuarterPrimitiveReduction.lean, lines 66–88; source file SHA-256 04116ba5236184358d50490faa8000ec249e62fb1c5665b6d82deee453cd3c82; theorem Couret.InterIA.Catalogue.Quarter.Primitive.gcd_support_reduction

import Definitions.Def_Couret_QuarterPrimitiveReduction_b041ef56a347
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MonoidAlgebra.Defs
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.Abel
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_coprime_not_both_even
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_nonaffine_iff_gcd
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_reduced_coprime
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Arithmetic_reduced_modulus_positive
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_patternA_dilate
import Theorems.Thm_Couret_InterIA_Catalogue_Quarter_Primitive_patternB_dilate
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0
import Definitions.Def_Couret_AffineEquivalenceTransport_fe8e73389d60
import Definitions.Def_Couret_QuarterArithmeticCore_9ead8b9209d0

set_option autoImplicit false
namespace Couret.InterIA.Catalogue.Quarter.Primitive
open Finset Couret.InterIA.NormalForm Couret.InterIA.Catalogue.Quarter
open Couret.InterIA.Catalogue.Quarter.Arithmetic

theorem gcd_support_reduction (q : ℕ) (hq : 0 < q) (x : ZMod (4*q))
    (hx : x ∉ badParameters q) (hna : ¬ AffineEquivalent (patternA q x) (patternB q x)) :
    ∃ d b a : ℕ, 0 < d ∧ 0 < b ∧ q=d*b ∧ x.val=d*a ∧ a.Coprime b ∧ b%4=2 ∧
      IsUnit (a : ZMod (4*b)) ∧
      (patternA b (a : ZMod (4*b))).image (dilate (4*q) d)=patternA q x ∧
      (patternB b (a : ZMod (4*b))).image (dilate (4*q) d)=patternB q x := by sorry


end Couret.InterIA.Catalogue.Quarter.Primitive
