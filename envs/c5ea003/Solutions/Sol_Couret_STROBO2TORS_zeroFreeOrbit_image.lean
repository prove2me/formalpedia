-- Prove2me | solution 1 for Couret.STROBO2TORS.zeroFreeOrbit_image
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:30:50.298645+00:00
-- url     : https://prove2.me/submissions/03db271f-1e16-493d-af96-39646d9bd283

import Aesop
import Definitions.Def_Couret_Strobo2TorsCardinality_32b8061f8d58
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Data.Finset.Powerset

set_option autoImplicit false

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]





















theorem zero_mem_translate_two_torsion (S : Finset G) (u : G) (hu : u + u = 0) :
    0 ∈ translateSupport S u ↔ u ∈ S := by
  constructor
  · intro h
    obtain ⟨x, hx, hxu⟩ := Finset.mem_image.mp h
    have hxeq : x = u := by
      calc
        x = (x + u) + u := by simp [add_assoc, hu]
        _ = u := by rw [hxu]; simp
    simpa [hxeq] using hx
  · intro h
    exact Finset.mem_image.mpr ⟨u, h, hu⟩

section Finite

variable [Fintype G]









































theorem p2m_local_zeroFreeOrbit_image (S : Finset G) :
    zeroFreeOrbit S = ((twoTorsion : Finset G).filter (fun u => u ∉ S)).image
      (fun u => translateSupport S u) := by
  ext T
  constructor
  · intro h
    obtain ⟨hO, hzero⟩ := Finset.mem_filter.mp h
    obtain ⟨u, hu, ht⟩ := (mem_torsionOrbit S T).mp hO
    have hnu : u ∉ S := by
      intro hs
      have hz := (zero_mem_translate_two_torsion S u hu).mpr hs
      rw [← ht] at hz
      exact hzero hz
    exact Finset.mem_image.mpr ⟨u,
      Finset.mem_filter.mpr ⟨(mem_twoTorsion u).mpr hu, hnu⟩, ht.symm⟩
  · intro h
    obtain ⟨u, hu, ht⟩ := Finset.mem_image.mp h
    obtain ⟨huH, huS⟩ := Finset.mem_filter.mp hu
    have hu2 := (mem_twoTorsion u).mp huH
    apply Finset.mem_filter.mpr
    constructor
    · exact (mem_torsionOrbit S T).mpr ⟨u, hu2, ht.symm⟩
    · intro hz
      rw [← ht] at hz
      exact huS ((zero_mem_translate_two_torsion S u hu2).mp hz)








/-! ## Exceptional offsets for a fixed nonzero 2-torsion direction

This section identifies and counts possible DIFFERENCES b-a for a fixed
direction d. These offset counts are separate from the global fibre counts
proved in Strobo2TorsEnumeration and the exceptional zero-free counts proved
in Strobo2TorsZeroFree. An offset count alone is not a count of fibres.
-/























end Finite
end Couret.STROBO2TORS



universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
    (@Couret.STROBO2TORS.zeroFreeOrbit.{p2m_u_0} G inst inst_1 inst_2 S)
    (@Finset.image.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G) (fun a b => @Finset.decidableEq.{p2m_u_0} G inst_1 a b)
      (fun u => @Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S u)
      (@Finset.filter.{p2m_u_0} G
        (fun u =>
          Not
            (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) S
              u))
        (fun a =>
          @instDecidableNot
            (@Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) S a)
            (@Finset.decidableMem.{p2m_u_0} G inst_1 a S))
        (@Couret.STROBO2TORS.twoTorsion.{p2m_u_0} G inst inst_1 inst_2))) := @_root_.Couret.STROBO2TORS.p2m_local_zeroFreeOrbit_image

