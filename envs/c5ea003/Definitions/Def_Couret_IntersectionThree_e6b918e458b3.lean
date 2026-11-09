-- Prove2me | Definitions.Def_Couret_IntersectionThree_e6b918e458b3
-- name    : Couret_IntersectionThree_e6b918e458b3
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:00:52.259864+00:00
-- url     : https://prove2.me/theorems/a7c93980-0a67-45cb-8472-1ce6fa6d50b9
-- title:
--   Algebraic support lemmas for three common points
-- statement:
--   This bundle provides the supporting group-algebra and coefficient calculations for two four-point supports sharing three points. It compares a common support with one exchanged atom and uses ordered-square equality to constrain the exchange. The statements serve the intersection-size reduction; the bundle does not introduce a new independent family predicate.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/IntersectionThree.lean; source file SHA-256 b3124b74c98f6b286643eb93c66bfec0060bc80c1705a4a9f43c218fe84883d2

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
import Definitions.Def_Couret_AntipodalFibres_0fc966ab17b4
import Definitions.Def_Couret_GroupRingBridge_e289cfa11c86
import Definitions.Def_Couret_TranslationControls_1ed5eea33a54

set_option autoImplicit false
namespace Couret.InterIA.IntersectionThree
open Finset Couret.InterIA.Parity Couret.InterIA.GroupRing Couret.InterIA.Fibres
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem indicator_insert (C : Finset G) (a : G) (ha : a ∉ C) :
    indicator (insert a C) = AddMonoidAlgebra.single a 1 + indicator C := by
  unfold indicator
  rw [Finset.sum_insert ha]

/-- Cancellation is only of the integer factor 2, never of a zero divisor. -/
theorem common_cross_term (C : Finset G) (a b : G) (ha : a ∉ C) (hb : b ∉ C)
    (hd : a+a=b+b)
    (hsquare : ∀ z, orderedSquare (insert a C) z = orderedSquare (insert b C) z) :
    AddMonoidAlgebra.single a 1 * indicator C =
      AddMonoidAlgebra.single b 1 * indicator C := by
  have he := (square_equality_iff (insert a C) (insert b C)).mpr hsquare
  rw [indicator_insert C a ha, indicator_insert C b hb] at he
  have hd' : (AddMonoidAlgebra.single a 1 : AddMonoidAlgebra ℤ G) *
      AddMonoidAlgebra.single a 1 = AddMonoidAlgebra.single b 1 *
      AddMonoidAlgebra.single b 1 := by
    simp only [AddMonoidAlgebra.single_mul_single, one_mul, hd]
  have hz : (2 : AddMonoidAlgebra ℤ G) *
      (AddMonoidAlgebra.single a 1 * indicator C -
        AddMonoidAlgebra.single b 1 * indicator C) = 0 := by
    calc
      _ = ((AddMonoidAlgebra.single a 1 + indicator C) *
          (AddMonoidAlgebra.single a 1 + indicator C) -
          (AddMonoidAlgebra.single b 1 + indicator C) *
          (AddMonoidAlgebra.single b 1 + indicator C)) -
          (AddMonoidAlgebra.single a 1 * AddMonoidAlgebra.single a 1 -
          AddMonoidAlgebra.single b 1 * AddMonoidAlgebra.single b 1) := by ring
      _ = 0 := by rw [he, hd']; simp
  exact sub_eq_zero.mp (integer_coefficient_no_two_torsion _ hz)

theorem common_part_stable (C : Finset G) (a h : G) (hh2 : h+h=0)
    (ha : a ∉ C) (hb : a+h ∉ C)
    (hsquare : ∀ z, orderedSquare (insert a C) z = orderedSquare (insert (a+h) C) z) :
    ∀ z ∈ C, z+h ∈ C := by
  have hd : a+a=(a+h)+(a+h) := by
    calc a+a = (a+a)+(h+h) := by rw [hh2,add_zero]
         _ = (a+h)+(a+h) := by abel
  have he := common_cross_term C a (a+h) ha hb hd hsquare
  intro z hz
  have hc := congrArg (fun f : AddMonoidAlgebra ℤ G => f.coeff (a+z+h)) he
  change (AddMonoidAlgebra.single a 1 * indicator C).coeff (a+z+h) =
    (AddMonoidAlgebra.single (a+h) 1 * indicator C).coeff (a+z+h) at hc
  rw [monomial_translate_coefficient, monomial_translate_coefficient] at hc
  have h1 : a+z+h-a=z+h := by abel
  have h2 : a+z+h-(a+h)=z := by abel
  rw [h1,h2,indicator_apply,indicator_apply] at hc
  by_contra hn
  simp [hz,hn] at hc



end Couret.InterIA.IntersectionThree


