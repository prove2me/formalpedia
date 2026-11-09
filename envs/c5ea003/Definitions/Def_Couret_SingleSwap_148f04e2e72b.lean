-- Prove2me | Definitions.Def_Couret_SingleSwap_148f04e2e72b
-- name    : Couret_SingleSwap_148f04e2e72b
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T19:01:14.196832+00:00
-- url     : https://prove2.me/theorems/07e66dee-c178-417a-bef1-4d9f5ca430f6
-- title:
--   Even common part under one antipodal exchange
-- statement:
--   Provides proved helper results for square-profile collisions with one exchanged point on each side. Under a nonzero half-turn and stability of the symmetric difference, the common part has even cardinality. In a positive even cyclic modulus, two colliding four-element supports consequently cannot have a three-element intersection.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/SingleSwap.lean; source file SHA-256 e3383e69cd7297f8889be28f527522076c49b30b4ad4047a2c7ec2230a566c63

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

/-- A single antipodal exchange forces the common support to have even cardinal. -/
theorem single_exchange_even_common (h : G) (hh : h ≠ 0) (hh2 : h+h=0)
    (S T : Finset G) (hS : (S \ T).card=1) (hT : (T \ S).card=1)
    (hstable : ∀ x ∈ symmDiff S T, x+h ∈ symmDiff S T)
    (hsquare : ∀ z, orderedSquare S z=orderedSquare T z) :
    (S ∩ T).card % 2 = 0 := by
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hS
  obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hT
  have haS : a ∈ S ∧ a ∉ T := Finset.mem_sdiff.mp (by rw [ha]; simp)
  have hbT : b ∈ T ∧ b ∉ S := Finset.mem_sdiff.mp (by rw [hb]; simp)
  have haC : a ∉ S ∩ T := by simp [haS]
  have hbC : b ∉ S ∩ T := by simp [hbT]
  have heS : S = insert a (S ∩ T) := by
    ext x
    have he : x ∈ S ∧ x ∉ T ↔ x=a := by
      rw [← Finset.mem_sdiff,ha]; simp
    simp only [mem_insert,mem_inter]
    tauto
  have heT : T = insert b (S ∩ T) := by
    ext x
    have he : x ∈ T ∧ x ∉ S ↔ x=b := by
      rw [← Finset.mem_sdiff,hb]; simp
    simp only [mem_insert,mem_inter]
    tauto
  have hD : a+h ∈ symmDiff S T :=
    hstable a (Finset.mem_symmDiff.mpr (Or.inl haS))
  have hab : a+h=b := by
    rcases Finset.mem_symmDiff.mp hD with hp|hp
    · have he : a+h=a := by
        have hx : a+h ∈ S \ T := Finset.mem_sdiff.mpr hp
        rw [ha] at hx
        exact Finset.mem_singleton.mp hx
      exact False.elim (hh (add_left_cancel (by simpa using he : a+h=a+0)))
    · have hx : a+h ∈ T \ S := Finset.mem_sdiff.mpr hp
      rw [hb] at hx
      exact Finset.mem_singleton.mp hx
  have hcs := common_part_stable (S ∩ T) a h hh2 haC (by rw [hab]; exact hbC)
    (by simpa only [hab,← heS,← heT] using hsquare)
  have hc := twice_fibres_card h hh hh2 (S ∩ T) hcs
  omega

/-- No lower bound on m beyond positivity and no congruence restriction. -/
theorem cyclic_four_intersection_ne_three (m : ℕ) (hm : 0 < m)
    (S T : Finset (ZMod (2*m))) (hS : S.card=4) (hT : T.card=4)
    (hsquare : ∀ z, orderedSquare S z=orderedSquare T z) :
    (S ∩ T).card ≠ 3 := by
  intro hI
  have h1 := Finset.card_sdiff_add_card_inter S T
  have h2 := Finset.card_sdiff_add_card_inter T S
  rw [Finset.inter_comm T S] at h2
  have he := single_exchange_even_common (m : ZMod (2*m))
    (Couret.InterIA.L4.half_ne_zero m hm) (Couret.InterIA.L4.half_add_half m)
    S T (by omega) (by omega)
    (fun x hx => (even_symmetric_difference_stable m hm S T hsquare x).mp hx) hsquare
  omega





end Couret.InterIA.IntersectionThree


