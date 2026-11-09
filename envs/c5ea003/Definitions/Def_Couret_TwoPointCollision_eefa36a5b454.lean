-- Prove2me | Definitions.Def_Couret_TwoPointCollision_eefa36a5b454
-- name    : Couret_TwoPointCollision_eefa36a5b454
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:55.947807+00:00
-- url     : https://prove2.me/theorems/8fcdd06b-48ab-469f-8fd0-30e814ee8b60
-- title:
--   Ordered-square coefficients of two-point supports
-- statement:
--   The indexed pair coefficient is
--
--   $$C_{a,b}(z)=[2a=z]+[2b=z]+2[a+b=z].$$
--
--   The bundle connects it to actual two-element supports when $a\ne b$, evaluates its diagonal and cross positions, and supplies transfer facts for equal doubled images. These elementary coefficient lemmas support the reduction of larger support-collision cases.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/TwoPointCollision.lean; source file SHA-256 2b544e811d91074c1143be0a41817cbd978462a670ca9d6c7b39cd133d16f371

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc

set_option autoImplicit false
namespace Couret.InterIA.TwoPoint
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

def pairCoeff (a b z : G) : ℕ :=
  (if a+a=z then 1 else 0)+(if b+b=z then 1 else 0)+
    2*(if a+b=z then 1 else 0)

theorem pair_coeff_comm (a b z : G) : pairCoeff a b z=pairCoeff b a z := by
  simp [pairCoeff,add_comm,add_left_comm]

theorem pair_sum_ne_left_double (a b : G) (hab : a ≠ b) : a+b ≠ a+a := by
  intro he
  exact hab (add_left_cancel he).symm

theorem pair_sum_ne_right_double (a b : G) (hab : a ≠ b) : a+b ≠ b+b := by
  intro he
  exact hab (add_right_cancel he)

theorem actual_pair_coefficient (a b z : G) (hab : a ≠ b) :
    orderedSquare ({a,b} : Finset G) z=pairCoeff a b z := by
  simp only [orderedSquare,Finset.sum_pair hab]
  unfold pairCoeff
  rw [add_comm b a]
  split_ifs <;> omega

theorem pair_coeff_at_sum (a b : G) (hab : a ≠ b) : pairCoeff a b (a+b)=2 := by
  simp [pairCoeff,(pair_sum_ne_left_double a b hab).symm,
    (pair_sum_ne_right_double a b hab).symm]

theorem pair_coeff_at_double_distinct (a b : G) (hab : a ≠ b)
    (hd : a+a ≠ b+b) : pairCoeff a b (a+a)=1 := by
  simp [pairCoeff,hd.symm,pair_sum_ne_left_double a b hab]

theorem pair_coeff_at_double_equal (a b : G) (hab : a ≠ b)
    (hd : a+a=b+b) : pairCoeff a b (a+a)=2 := by
  simp [pairCoeff,hd.symm,pair_sum_ne_left_double a b hab]

theorem matched_double_forces_center (a b c d : G) (hab : a ≠ b)
    (hd : a+a ≠ b+b)
    (heq : ∀ z, pairCoeff a b z=pairCoeff c d z)
    (hc : c+c=a+a) : c+d=a+b := by
  have hp := heq (a+b)
  rw [pair_coeff_at_sum a b hab] at hp
  have hc0 : c+c ≠ a+b := by
    rw [hc]
    exact (pair_sum_ne_left_double a b hab).symm
  by_contra hcenter
  simp only [pairCoeff,if_neg hc0,if_neg hcenter,zero_add,mul_zero,add_zero] at hp
  split_ifs at hp <;> omega



theorem equal_doubles_transfer (a b c d : G) (hcd : c ≠ d)
    (hd : a+a=b+b)
    (heq : ∀ z, pairCoeff a b z=pairCoeff c d z) : c+c=d+d := by
  by_contra hne
  have hp := heq (c+c)
  rw [pair_coeff_at_double_distinct c d hcd hne] at hp
  have hba : b+b=a+a := hd.symm
  simp only [pairCoeff,hba] at hp
  split_ifs at hp <;> omega

theorem equal_doubles_positions (a b z : G) (hd : a+a=b+b)
    (hp : pairCoeff a b z=2) : a+a=z ∨ a+b=z := by
  by_contra hn
  have h1 : a+a ≠ z := by tauto
  have h2 : a+b ≠ z := by tauto
  have h3 : b+b ≠ z := by rw [← hd]; exact h1
  simp [pairCoeff,h1,h2,h3] at hp











end Couret.InterIA.TwoPoint


