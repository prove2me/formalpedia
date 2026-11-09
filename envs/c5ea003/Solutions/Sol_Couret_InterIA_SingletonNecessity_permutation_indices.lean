-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.permutation_indices
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:01:51.801796+00:00
-- url     : https://prove2.me/submissions/361a38e4-aecd-426c-9c51-a002db446c04

import Definitions.Def_Couret_CertificateSoundness_1059e04412f7
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity

theorem map_range_getElem_bang {α : Type*} [Inhabited α] (l : List α) :
    (List.range l.length).map (fun j => l[j]!)=l := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_map,List.getElem_range]
    exact getElem!_pos l i hj

theorem p2m_local_permutation_indices {α : Type*} [Inhabited α] (L R : List α)
    (h : L.Perm R) :
    ∃ p : List ℕ, p.Perm (List.range R.length) ∧ L=p.map (fun j => R[j]!) := by
  let f : ℕ → α := fun j => R[j]!
  have h' : L.Perm ((List.range R.length).map f) := by
    rw [map_range_getElem_bang]
    exact h
  have hc : Relation.Comp (fun a b => a=b.map f) List.Perm L (List.range R.length) := by
    rw [List.eq_map_comp_perm f]
    exact h'
  obtain ⟨p,hp1,hp2⟩ := hc
  exact ⟨p,hp2,hp1⟩



end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} [inst : Inhabited.{p2m_u_0 + 1} α] (L R : List.{p2m_u_0} α),
  @List.Perm.{p2m_u_0} α L R →
    @Exists.{1} (List.{0} Nat) fun p =>
      And (@List.Perm.{0} Nat p (List.range (@List.length.{p2m_u_0} α R)))
        (@Eq.{p2m_u_0 + 1} (List.{p2m_u_0} α) L
          (@List.map.{0, p2m_u_0} Nat α
            (fun j =>
              @GetElem?.getElem!.{p2m_u_0, 0, p2m_u_0} (List.{p2m_u_0} α) Nat α
                (fun as i => @LT.lt.{0} Nat instLTNat i (@List.length.{p2m_u_0} α as))
                (@List.instGetElem?NatLtLength.{p2m_u_0} α) inst R j)
            p)) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_permutation_indices

