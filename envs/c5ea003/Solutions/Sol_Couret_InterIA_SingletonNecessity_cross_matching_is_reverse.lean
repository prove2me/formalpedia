-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.cross_matching_is_reverse
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:07:14.778825+00:00
-- url     : https://prove2.me/submissions/f13cbdf5-cd17-4435-b733-83ba3142027a

import Definitions.Def_Couret_MatchingElimination_8675038abe55
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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_certificate_sound
import Theorems.Thm_Couret_InterIA_SingletonNecessity_crossData_coverage
import Theorems.Thm_Couret_InterIA_SingletonNecessity_crossData_valid
import Definitions.Def_Couret_MatchingCertificateData_656be71337d8
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
variable {G : Type*} [AddCommGroup G]

theorem cross_certificate_exists (p : List ℕ) (hp : p.Perm (List.range 6)) :
    p=reversePerm ∨ ∃ c : Certificate, c.perm=p ∧ valid false c=true := by
  have hm : p ∈ crossData.map Certificate.perm := by
    rw [crossData_coverage]
    exact List.mem_permutations'.mpr hp
  obtain ⟨c,hc,hcp⟩ := List.mem_map.mp hm
  have hv := List.all_eq_true.mp crossData_valid c hc
  simp only [crossValid,Bool.or_eq_true,decide_eq_true_eq] at hv
  rcases hv with hv|hv
  · exact Or.inl (hcp.symm.trans hv)
  · exact Or.inr ⟨c,hcp,hv⟩







theorem valid_certificate_contradicts_distinct (mixed : Bool) (c : Certificate)
    (hc : valid mixed c=true) (x : Fin 6 → G) (hd : DistinctLabels x)
    (hr : RelationsHold x mixed c.perm) : False := by
  obtain ⟨hij,hj,heq⟩ := certificate_sound mixed c hc x hr
  have hi : c.i<7 := lt_trans hij hj
  have h : (⟨c.i,hi⟩ : Fin 7) = ⟨c.j,hj⟩ := hd heq
  have he : c.i=c.j := congrArg Fin.val h
  exact (Nat.ne_of_lt hij) he

theorem p2m_local_cross_matching_is_reverse (x : Fin 6 → G) (hd : DistinctLabels x)
    (p : List ℕ) (hp : p.Perm (List.range 6))
    (hr : RelationsHold x false p) : p=reversePerm := by
  rcases cross_certificate_exists p hp with h|⟨c,hp,hc⟩
  · exact h
  · exact False.elim (valid_certificate_contradicts_distinct false c hc x hd (hp ▸ hr))



end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
  @Couret.InterIA.SingletonNecessity.DistinctLabels.{p2m_u_0} G inst x →
    ∀ (p : List.{0} Nat),
      @List.Perm.{0} Nat p (List.range (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))) →
        @Couret.InterIA.SingletonNecessity.RelationsHold.{p2m_u_0} G inst x Bool.false p →
          @Eq.{1} (List.{0} Nat) p Couret.InterIA.SingletonNecessity.reversePerm := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_cross_matching_is_reverse

