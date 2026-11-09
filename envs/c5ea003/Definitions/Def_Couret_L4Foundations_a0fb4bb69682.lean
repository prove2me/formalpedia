-- Prove2me | Definitions.Def_Couret_L4Foundations_a0fb4bb69682
-- name    : Couret_L4Foundations_a0fb4bb69682
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:09.335575+00:00
-- url     : https://prove2.me/theorems/a9bfde4f-4bcf-45b6-b067-b8b496219f03
-- title:
--   Half-turn arithmetic and elementary collision identities
-- statement:
--   This bundle supplies elementary facts for cyclic four-support analysis: the half-period in $\mathbb Z/(2m)\mathbb Z$ is a nonzero involution when $m>0$, and the doubling kernel consists of zero and that half-period. It also gives the rectangle-side consequence of a two-element doubling kernel.
--
--   For a commutative-ring involution $H^2=1$, it includes $(1+H)^2=2(1+H)$, $(1+H)(1-H)=0$, and the corresponding mixed-case expansion. These are the arithmetic and algebraic foundations of the later collision classifications.
-- source:
--   Alexandre Couret, Couret — Additive reconstruction: STROBO-4, singleton collisions and RECOH formal proof artifacts, https://zenodo.org/records/23980513; archive COURET_MATHEMATIQUES_20261105.zip, SHA-256 19a3b59aee930df74cab79c27b29e014843bd17179a26fef1261ed6b5a651ab7; file source-tree/research/interia/m026-1-catalogue-equivalence-20261103/L4Foundations.lean; source file SHA-256 a80b43da8931fa1cb12280548eeb0978b71553697ecec5546d5732de3fbdf552

import Mathlib.Data.Finset.Insert
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

set_option autoImplicit false

namespace Couret.InterIA.L4

section Cyclic

theorem half_ne_zero (m : ℕ) (hm : 0 < m) :
    (m : ZMod (2*m)) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at hv
  omega

theorem half_add_half (m : ℕ) :
    (m : ZMod (2*m)) + m = 0 := by
  rw [← Nat.cast_add]
  convert ZMod.natCast_self (2*m) using 1 <;> congr 1 <;> omega

theorem doubling_kernel (m : ℕ) (hm : 0 < m) (x : ZMod (2*m))
    (hx : x+x=0) : x=0 ∨ x=(m : ZMod (2*m)) := by
  letI : NeZero (2*m) := ⟨by omega⟩
  have hv : x.val < 2*m := ZMod.val_lt x
  by_cases hsmall : x.val+x.val < 2*m
  · left
    have he := ZMod.val_add_of_lt hsmall
    rw [hx, ZMod.val_zero] at he
    have hz : x.val=0 := by omega
    exact ZMod.val_injective (2*m) (by simpa using hz)
  · right
    have he := ZMod.val_add_of_le (by omega : 2*m ≤ x.val+x.val)
    rw [hx, ZMod.val_zero] at he
    have heq : x.val=m := by omega
    apply ZMod.val_injective (2*m)
    simpa only [ZMod.val_natCast_of_lt (by omega : m < 2*m)] using heq

end Cyclic

section Rectangle
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

/-- Only support closure is needed; equality of positive rectangle multisets is stronger. -/
theorem rectangle_side (h : G) (hh : h ≠ 0) (hh2 : h+h=0)
    (hkernel : ∀ x : G, x+x=0 → x=0 ∨ x=h)
    (w d e : G)
    (hclosed : ∀ x ∈ ({w,w+d,w+e,w+d+e} : Finset G),
      x+h ∈ ({w,w+d,w+e,w+d+e} : Finset G)) :
    d=0 ∨ d=h ∨ e=0 ∨ e=h := by
  by_contra hn
  have hd0 : d ≠ 0 := by tauto
  have hdh : d ≠ h := by tauto
  have he0 : e ≠ 0 := by tauto
  have heh : e ≠ h := by tauto
  have hp := hclosed w (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  have hsum : d+e=h := by
    rcases hp with hp|hp|hp|hp
    · exact False.elim (hh (add_left_cancel (by simpa using hp : w+h=w+0)))
    · exact False.elim (hdh (add_left_cancel hp).symm)
    · exact False.elim (heh (add_left_cancel hp).symm)
    · have hp' : w+h=w+(d+e) := by simpa only [add_assoc] using hp
      exact (add_left_cancel hp').symm
  have hq := hclosed (w+d) (by simp)
  simp only [Finset.mem_insert, Finset.mem_singleton] at hq
  have hdiff : e-d=h := by
    rcases hq with hq|hq|hq|hq
    · have hq' : d+h=0 := add_left_cancel (by simpa only [add_assoc, add_zero] using hq : w+(d+h)=w+0)
      exact False.elim (hdh (by
        calc d = d+(h+h) := by rw [hh2,add_zero]
             _ = (d+h)+h := by abel
             _ = h := by rw [hq',zero_add]))
    · exact False.elim (hh (add_left_cancel (by simpa using hq : (w+d)+h=(w+d)+0)))
    · have hq' : d+h=e := add_left_cancel (by simpa only [add_assoc] using hq)
      calc e-d = (d+h)-d := by rw [hq']
           _ = h := by abel
    · exact False.elim (heh (add_left_cancel hq).symm)
  have hd2 : d+d=0 := by
    calc d+d = (d+e)-(e-d) := by abel
         _ = h-h := by rw [hsum,hdiff]
         _ = 0 := sub_self h
  exact (hkernel d hd2).elim hd0 hdh

end Rectangle



section Algebra
variable {R : Type*} [CommRing R]

theorem antipodal_square (H : R) (hH : H*H=1) :
    (1+H)*(1+H)=2*(1+H) := by
  calc (1+H)*(1+H) = 1+2*H+H*H := by ring
       _ = 2*(1+H) := by rw [hH]; ring

theorem antipodal_cross (H : R) (hH : H*H=1) :
    (1+H)*(1-H)=0 := by
  calc (1+H)*(1-H)=1-H*H := by ring
       _=0 := by rw [hH]; ring

theorem mixed_case_identity (H a b c q : R) (hH : H*H=1) :
    ((1+H)*(a-b)+(1-H)*q)*(2*c+(1+H)*(a+b+q)) =
      2*((1+H)*(a-b)*(c+a+b+q)+(1-H)*q*c) := by
  have hs := antipodal_square H hH
  have hc := antipodal_cross H hH
  calc
    _ = 2*(1+H)*(a-b)*c + ((1+H)*(1+H))*(a-b)*(a+b+q) +
      2*(1-H)*q*c + ((1+H)*(1-H))*q*(a+b+q) := by ring
    _ = _ := by rw [hs,hc]; ring



end Algebra

section IntegerCoefficients
variable {α : Type*}





end IntegerCoefficients

end Couret.InterIA.L4


