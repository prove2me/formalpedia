-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.mixed_matching_impossible
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:18:12.587322+00:00
-- url     : https://prove2.me/submissions/83515daf-8ab9-457a-9ab0-a7d338df146a

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
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedData_coverage
import Theorems.Thm_Couret_InterIA_SingletonNecessity_mixedData_valid
import Definitions.Def_Couret_MatchingCertificateData_656be71337d8
import Definitions.Def_Couret_CertificateSoundness_1059e04412f7

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
variable {G : Type*} [AddCommGroup G]



theorem mixed_certificate_exists (p : List ℕ) (hp : p.Perm (List.range 7)) :
    ∃ c : Certificate, c.perm=p ∧ valid true c=true := by
  have hm : p ∈ mixedData.map Certificate.perm := by
    rw [mixedData_coverage]
    exact List.mem_permutations'.mpr hp
  obtain ⟨c,hc,hcp⟩ := List.mem_map.mp hm
  exact ⟨c,hcp,List.all_eq_true.mp mixedData_valid c hc⟩





theorem valid_certificate_contradicts_distinct (mixed : Bool) (c : Certificate)
    (hc : valid mixed c=true) (x : Fin 6 → G) (hd : DistinctLabels x)
    (hr : RelationsHold x mixed c.perm) : False := by
  obtain ⟨hij,hj,heq⟩ := certificate_sound mixed c hc x hr
  have hi : c.i<7 := lt_trans hij hj
  have h : (⟨c.i,hi⟩ : Fin 7) = ⟨c.j,hj⟩ := hd heq
  have he : c.i=c.j := congrArg Fin.val h
  exact (Nat.ne_of_lt hij) he



theorem p2m_local_mixed_matching_impossible (x : Fin 6 → G) (hd : DistinctLabels x)
    (p : List ℕ) (hp : p.Perm (List.range 7))
    (hr : RelationsHold x true p) : False := by
  obtain ⟨c,hp,hc⟩ := mixed_certificate_exists p hp
  exact valid_certificate_contradicts_distinct true c hc x hd (hp ▸ hr)

end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
  @Couret.InterIA.SingletonNecessity.DistinctLabels.{p2m_u_0} G inst x →
    ∀ (p : List.{0} Nat),
      @List.Perm.{0} Nat p (List.range (@OfNat.ofNat.{0} Nat (nat_lit 7) (instOfNatNat (nat_lit 7)))) →
        @Couret.InterIA.SingletonNecessity.RelationsHold.{p2m_u_0} G inst x Bool.true p → False := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_mixed_matching_impossible

