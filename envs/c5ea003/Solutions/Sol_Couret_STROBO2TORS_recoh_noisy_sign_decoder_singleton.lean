-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_noisy_sign_decoder_singleton
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:28:44.223231+00:00
-- url     : https://prove2.me/submissions/f9373f26-855b-4cdc-91c8-b7ff31f7cb72

import Aesop
import Definitions.Def_Couret_RecohNoisySignRecovery_25d41afc9bfe
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_recover_support_eq
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_recovered_candidates_square_sound
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_noisy_decoder_singleton
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8
import Definitions.Def_Couret_RecohIndexedSignRecovery_d641979954b3

set_option autoImplicit false

/-!
Noisy sign recovery from a list of square-fibre representatives.  Each
binary sign is recovered by one rational ball test, then transported through
the existing two-torsion coordinate equivalence.  At most one candidate is
created per representative, without enumerating the two-torsion subgroup.
The rational decoder in RecohNoisyUniqueness supplies the final tolerance
filter and uniqueness contract.
-/

namespace Couret.STROBO2TORS







variable {G J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2









/-- Any true support represented by the list survives the candidate
generation stage under the stated measurement and prediction budgets. -/
theorem recoh_noisy_recovered_candidates_complete
    (representatives : Finset (Finset G)) (bank : J → AddChar G ℂ)
    (e : H₂ ≃+ (J → ZMod 2))
    (hcoord : ∀ (u : H₂) (i : J), bank i (u : G) = if e u i = 0 then 1 else -1)
    (predicted : Finset G → J → RecohRationalComplex)
    (observed : J → RecohRationalComplex) (radius : ℚ) (ε η : ℝ)
    (hradius : 0 ≤ radius) (B : Finset G) (hB : B ∈ representatives) (u : H₂)
    (hamplitude : ∀ i, 1 ≤ ‖recohSupportProbe (bank i) B‖)
    (hpred : ∀ i, ‖recohRationalComplexValue (predicted B i) -
      recohSupportProbe (bank i) B‖ ≤ η)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) -
      recohSupportProbe (bank i) (translateSupport B (u : G))‖ ≤ ε)
    (hcomplete : ε + η ≤ (radius : ℝ))
    (hunique : ε + ((radius : ℝ) + η) < 2) :
    translateSupport B (u : G) ∈
      recohNoisyRecoveredCandidates representatives e predicted observed radius := by
  apply Finset.mem_image.mpr
  exact ⟨B, hB, recoh_noisy_recover_support_eq bank e hcoord predicted observed
    radius ε η hradius B u hamplitude hpred hobs hcomplete hunique⟩









/-- End-to-end singleton contract from a covering list of representatives.
The proof includes noisy sign recovery, exact square preservation, the
rational final filter, and the strict total error budget. -/
theorem p2m_local_recoh_noisy_sign_decoder_singleton [Fintype G]
    {I : Type*} [Fintype I]
    (bank : I → AddChar G ℂ) (S : Finset G) (representatives : Finset (Finset G))
    (hrepresentatives : representatives ⊆ squareFibre S)
    (hcover : ∃ B ∈ representatives, OrdinaryPartner B S)
    (e : H₂ ≃+ (J → ZMod 2)) (index : J → I)
    (hcoord : ∀ (u : H₂) (j : J), bank (index j) (u : G) = if e u j = 0 then 1 else -1)
    (predicted : Finset G → I → RecohRationalComplex)
    (observed : I → RecohRationalComplex) (radius : ℚ) (ε η : ℝ)
    (hradius : 0 ≤ radius) (hη : 0 ≤ η)
    (hsep : RecohProbeSeparated bank (squareFibre S) 2)
    (hamplitude : ∀ B ∈ representatives, ∀ j, 1 ≤ ‖recohSupportProbe (bank (index j)) B‖)
    (hpred : ∀ T ∈ squareFibre S, ∀ i,
      ‖recohRationalComplexValue (predicted T i) - recohSupportProbe (bank i) T‖ ≤ η)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) - recohSupportProbe (bank i) S‖ ≤ ε)
    (hcomplete : ε + η ≤ (radius : ℝ))
    (hunique : 2 * ((radius : ℝ) + η) < 2) :
    recohNoisySignDecoder representatives e index predicted observed radius = {S} := by
  let candidates := recohNoisyRecoveredCandidates representatives e
    (fun B j => predicted B (index j)) (fun j => observed (index j)) radius
  have hsubset : candidates ⊆ squareFibre S :=
    recoh_noisy_recovered_candidates_square_sound S representatives hrepresentatives e _ _ radius
  have hSmem : S ∈ candidates := by
    obtain ⟨B, hB, u, hu, hS⟩ := hcover
    let u2 : H₂ := ⟨u, by simpa only [recoh_mem_torsion_subgroup, two_nsmul] using hu⟩
    have hmem := recoh_noisy_recovered_candidates_complete representatives
      (fun j => bank (index j)) e hcoord
      (fun B j => predicted B (index j)) (fun j => observed (index j)) radius ε η
      hradius B hB u2 (hamplitude B hB)
      (fun j => hpred B (hrepresentatives hB) (index j))
      (fun j => by simpa [u2, ← hS] using hobs (index j)) hcomplete
      (by linarith)
    simpa [candidates, u2, ← hS] using hmem
  apply recoh_rational_noisy_decoder_singleton
    (fun T i => recohSupportProbe (bank i) T) candidates predicted observed
    radius ε η 2 hradius S hSmem
  · intro B hB C hC hBC
    exact hsep B (hsubset hB) C (hsubset hC) hBC
  · intro T hT i
    exact hpred T (hsubset hT) i
  · exact hobs
  · exact hcomplete
  · exact hunique

end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {G : Type p2m_u_0} {J : Type p2m_u_1} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] {I : Type p2m_u_2} [inst_3 : Fintype.{p2m_u_2} I]
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (S : Finset.{p2m_u_0} G) (representatives : Finset.{p2m_u_0} (Finset.{p2m_u_0} G)),
  @HasSubset.Subset.{p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@Finset.instHasSubset.{p2m_u_0} (Finset.{p2m_u_0} G)) representatives
      (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S) →
    (@Exists.{p2m_u_0 + 1} (Finset.{p2m_u_0} G) fun B =>
        And
          (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
              (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
            representatives B)
          (@Couret.STROBO2TORS.OrdinaryPartner.{p2m_u_0} G inst inst_1 B S)) →
      ∀
        (e :
          @AddEquiv.{p2m_u_0, p2m_u_1}
            (@Subtype.{p2m_u_0 + 1} G fun x =>
              @Membership.mem.{p2m_u_0, p2m_u_0} G
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                  (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                  (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                x)
            (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
              (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
            (@Pi.instAdd.{p2m_u_1, 0} J (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              fun i =>
              @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@Semifield.toDivisionSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                          Nat.fact_prime_two)))))))
        (index : J → I),
        (∀
            (u :
              @Subtype.{p2m_u_0 + 1} G fun x =>
                @Membership.mem.{p2m_u_0, p2m_u_0} G
                  (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                  (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                    (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                  (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  x)
            (j : J),
            @Eq.{1} Complex
              (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                (@AddChar.{p2m_u_0, 0} G
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                  Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                G (fun x => Complex)
                (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
                  (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
                    (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                  (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
                (bank (index j))
                (@Subtype.val.{p2m_u_0 + 1} G
                  (fun x =>
                    @Membership.mem.{p2m_u_0, p2m_u_0} G
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                      (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                        (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                      (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      x)
                  u))
              (@ite.{1} Complex
                (@Eq.{1} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                    (@AddEquiv.{p2m_u_0, p2m_u_1}
                      (@Subtype.{p2m_u_0 + 1} G fun x =>
                        @Membership.mem.{p2m_u_0, p2m_u_0} G
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                          (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                            (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          x)
                      (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Pi.instAdd.{p2m_u_1, 0} J
                        (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                        @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@instDistribOfSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@DivisionSemiring.toSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Semifield.toDivisionSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@Field.toSemifield.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    Nat.fact_prime_two)))))))
                    (@Subtype.{p2m_u_0 + 1} G fun x =>
                      @Membership.mem.{p2m_u_0, p2m_u_0} G
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                          (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        x)
                    (fun x => J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@EquivLike.toFunLike.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                      (@AddEquiv.{p2m_u_0, p2m_u_1}
                        (@Subtype.{p2m_u_0 + 1} G fun x =>
                          @Membership.mem.{p2m_u_0, p2m_u_0} G
                            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            x)
                        (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Pi.instAdd.{p2m_u_1, 0} J
                          (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                          @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@instDistribOfSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@DivisionSemiring.toSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@Semifield.toDivisionSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@Field.toSemifield.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      Nat.fact_prime_two)))))))
                      (@Subtype.{p2m_u_0 + 1} G fun x =>
                        @Membership.mem.{p2m_u_0, p2m_u_0} G
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                          (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                            (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          x)
                      (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddEquiv.instEquivLike.{p2m_u_0, p2m_u_1}
                        (@Subtype.{p2m_u_0 + 1} G fun x =>
                          @Membership.mem.{p2m_u_0, p2m_u_0} G
                            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            x)
                        (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Pi.instAdd.{p2m_u_1, 0} J
                          (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                          @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@instDistribOfSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@DivisionSemiring.toSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@Semifield.toDivisionSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@Field.toSemifield.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      Nat.fact_prime_two))))))))
                    e u j)
                  (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@instMulZeroClassOfSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@DivisionSemiring.toSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Semifield.toDivisionSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Field.toSemifield.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  Nat.fact_prime_two)))))))))
                (ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                  (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                    (@AddEquiv.{p2m_u_0, p2m_u_1}
                      (@Subtype.{p2m_u_0 + 1} G fun x =>
                        @Membership.mem.{p2m_u_0, p2m_u_0} G
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                          (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                            (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          x)
                      (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                      (@Pi.instAdd.{p2m_u_1, 0} J
                        (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                        @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@instDistribOfSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@DivisionSemiring.toSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Semifield.toDivisionSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@Field.toSemifield.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                    Nat.fact_prime_two)))))))
                    (@Subtype.{p2m_u_0 + 1} G fun x =>
                      @Membership.mem.{p2m_u_0, p2m_u_0} G
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                          (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        x)
                    (fun x => J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@EquivLike.toFunLike.{max (p2m_u_0 + 1) (p2m_u_1 + 1), p2m_u_0 + 1, p2m_u_1 + 1}
                      (@AddEquiv.{p2m_u_0, p2m_u_1}
                        (@Subtype.{p2m_u_0 + 1} G fun x =>
                          @Membership.mem.{p2m_u_0, p2m_u_0} G
                            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            x)
                        (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Pi.instAdd.{p2m_u_1, 0} J
                          (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                          @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@instDistribOfSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@DivisionSemiring.toSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@Semifield.toDivisionSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@Field.toSemifield.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      Nat.fact_prime_two)))))))
                      (@Subtype.{p2m_u_0 + 1} G fun x =>
                        @Membership.mem.{p2m_u_0, p2m_u_0} G
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                          (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                            (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          x)
                      (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@AddEquiv.instEquivLike.{p2m_u_0, p2m_u_1}
                        (@Subtype.{p2m_u_0 + 1} G fun x =>
                          @Membership.mem.{p2m_u_0, p2m_u_0} G
                            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                            (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                              (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                              (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                            (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            x)
                        (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                        (@Pi.instAdd.{p2m_u_1, 0} J
                          (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                          @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@instDistribOfSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@DivisionSemiring.toSemiring.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@Semifield.toDivisionSemiring.{0}
                                  (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (@Field.toSemifield.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      Nat.fact_prime_two))))))))
                    e u j)
                  (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                    (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@instMulZeroClassOfSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@DivisionSemiring.toSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Semifield.toDivisionSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Field.toSemifield.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  Nat.fact_prime_two)))))))))
                (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
                (@Neg.neg.{0} Complex Complex.instNeg
                  (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))))) →
          ∀ (predicted : Finset.{p2m_u_0} G → I → Couret.STROBO2TORS.RecohRationalComplex)
            (observed : I → Couret.STROBO2TORS.RecohRationalComplex) (radius : Rat) (ε η : Real),
            @LE.le.{0} Rat Rat.instLE (@OfNat.ofNat.{0} Rat (nat_lit 0) (@Rat.instOfNat (nat_lit 0))) radius →
              @LE.le.{0} Real Real.instLE (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero))
                  η →
                @Couret.STROBO2TORS.RecohProbeSeparated.{p2m_u_0, p2m_u_2} G inst I bank
                    (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S)
                    (@OfNat.ofNat.{0} Real (nat_lit 2)
                      (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
                  (∀ (B : Finset.{p2m_u_0} G),
                      @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                            (Finset.{p2m_u_0} G) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
                          representatives B →
                        ∀ (j : J),
                          @LE.le.{0} Real Real.instLE
                            (@OfNat.ofNat.{0} Real (nat_lit 1) (@One.toOfNat1.{0} Real Real.instOne))
                            (@Norm.norm.{0} Complex Complex.instNorm
                              (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank (index j)) B))) →
                    (∀ (T : Finset.{p2m_u_0} G),
                        @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                              (Finset.{p2m_u_0} G) (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
                            (@Couret.STROBO2TORS.squareFibre.{p2m_u_0} G inst inst_1 inst_2 S) T →
                          ∀ (i : I),
                            @LE.le.{0} Real Real.instLE
                              (@Norm.norm.{0} Complex Complex.instNorm
                                (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                                  (Couret.STROBO2TORS.recohRationalComplexValue (predicted T i))
                                  (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) T)))
                              η) →
                      (∀ (i : I),
                          @LE.le.{0} Real Real.instLE
                            (@Norm.norm.{0} Complex Complex.instNorm
                              (@HSub.hSub.{0, 0, 0} Complex Complex Complex (@instHSub.{0} Complex Complex.instSub)
                                (Couret.STROBO2TORS.recohRationalComplexValue (observed i))
                                (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) S)))
                            ε) →
                        @LE.le.{0} Real Real.instLE
                            (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) ε η)
                            (@Rat.cast.{0} Real Real.instRatCast radius) →
                          @LT.lt.{0} Real Real.instLT
                              (@HMul.hMul.{0, 0, 0} Real Real Real (@instHMul.{0} Real Real.instMul)
                                (@OfNat.ofNat.{0} Real (nat_lit 2)
                                  (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                    (@Nat.instAtLeastTwoHAddOfNat
                                      (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                      (@Nat.instNeZeroSucc
                                        (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                                  (@Rat.cast.{0} Real Real.instRatCast radius) η))
                              (@OfNat.ofNat.{0} Real (nat_lit 2)
                                (@instOfNatAtLeastTwo.{0} Real (nat_lit 2) Real.instNatCast
                                  (@Nat.instAtLeastTwoHAddOfNat
                                    (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                    (@Nat.instNeZeroSucc
                                      (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))))))) →
                            @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                              (@Couret.STROBO2TORS.recohNoisySignDecoder.{p2m_u_0, p2m_u_1, p2m_u_2} G J inst inst_1 I
                                inst_3 representatives e index predicted observed radius)
                              (@Singleton.singleton.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G)
                                (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                                (@Finset.instSingleton.{p2m_u_0} (Finset.{p2m_u_0} G)) S) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_noisy_sign_decoder_singleton

