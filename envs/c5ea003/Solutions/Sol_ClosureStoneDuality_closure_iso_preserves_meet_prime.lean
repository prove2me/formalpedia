-- Prove2me | solution 1 for ClosureStoneDuality.closure_iso_preserves_meet_prime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T23:48:49.269793+00:00
-- url     : https://prove2.me/submissions/67c2a681-15f4-4167-80e8-b7ef2f0dcff3

import Mathlib
import Definitions.Def_Bridges_ClosureStoneRealizationDuality

open Set Finset
open ClosureStoneDuality

variable {X : Type*} {Y : Type*}

theorem solution [Fintype X] [DecidableEq X]
    [Fintype Y] [DecidableEq Y]
    {clX : Set X → Set X} {clY : Set Y → Set Y}
    (_hX : IsClosureOperator clX) (_hY : IsClosureOperator clY)
    (e : ClosureTableIso clX clY) {P : Set X} (hP : IsMeetPrimeClosed clX P) :
    IsMeetPrimeClosed clY (Set.image e.toFun P) := by
  have hinj : Function.Injective e.toFun := by
    intro x y h
    have h' := congrArg e.invFun h
    simpa only [e.left_inv] using h'
  have himage (A : Set Y) : e.toFun '' (e.toFun ⁻¹' A) = A := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hy
      refine ⟨e.invFun y, ?_, e.right_inv y⟩
      change e.toFun (e.invFun y) ∈ A
      rw [e.right_inv]
      exact hy
  have hpull (A : Set Y) (hA : ClosureStoneDuality.IsClosed clY A) :
      ClosureStoneDuality.IsClosed clX (e.toFun ⁻¹' A) := by
    change clX (e.toFun ⁻¹' A) = e.toFun ⁻¹' A
    have hc : e.toFun '' clX (e.toFun ⁻¹' A) = A := by
      rw [e.commutes, himage]
      exact hA
    apply Set.Subset.antisymm
    · intro x hx
      change e.toFun x ∈ A
      rw [← hc]
      exact ⟨x, hx, rfl⟩
    · exact _hX.extensive _
  refine ⟨?_, ?_, ?_⟩
  · change clY (e.toFun '' P) = e.toFun '' P
    rw [← e.commutes, hP.1]
  · intro hfull
    apply hP.2.1
    apply Set.Subset.antisymm (Set.subset_univ _)
    intro x _
    have hx : e.toFun x ∈ e.toFun '' P := by
      rw [hfull]
      trivial
    rcases hx with ⟨p, hp, heq⟩
    exact hinj heq ▸ hp
  · intro A B hA hB hAB
    have hpre : (e.toFun ⁻¹' A) ∩ (e.toFun ⁻¹' B) ⊆ P := by
      intro x hx
      rcases hAB hx with ⟨p, hp, heq⟩
      exact hinj heq ▸ hp
    rcases hP.2.2 (hpull A hA) (hpull B hB) hpre with ha | hb
    · left
      intro y hy
      refine ⟨e.invFun y, ha ?_, e.right_inv y⟩
      change e.toFun (e.invFun y) ∈ A
      rw [e.right_inv]
      exact hy
    · right
      intro y hy
      refine ⟨e.invFun y, hb ?_, e.right_inv y⟩
      change e.toFun (e.invFun y) ∈ B
      rw [e.right_inv]
      exact hy
