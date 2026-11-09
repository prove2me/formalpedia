-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_sign_fast_decoder_eq_exact
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:28.700064+00:00
-- url     : https://prove2.me/submissions/bbc132cb-24cb-4533-9404-eb60b28b0437

import Aesop
import Definitions.Def_Couret_RecohFastDecoder_5bb89f11acce
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
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
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_fast_candidates_complete
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_exact_decoder_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_sign_recovery_spec
import Definitions.Def_Couret_RecohDecoderBounds_60ec29457baa
import Definitions.Def_Couret_RecohCyclicHalves_383c4510168a
import Definitions.Def_Couret_RecohSignRecovery_71a8a4a1ce8a

set_option autoImplicit false

/-!
One-representative RECOH decoder on an explicitly supplied finite support.

The construction visits only the three-element subsets of U.  A supplied
doubling solver chooses one half-sum for each feasible edge set, and a
translation-recovery function turns the corresponding representative into
one candidate.  The final filter uses the complete labelled observation.
No enumeration of the ambient group or its two-torsion subgroup occurs in
these definitions.  Their construction needs no Fintype instance on G.

The refinement theorem proves equality with recohExactDecoder, provided U
covers the observed square support and the half-sum and recovery contracts
hold.  Sign recovery supplies the recovery contract for binary coordinates
inside any larger labelled character bank.  Complex equality remains
noncomputable here: this is a Lean refinement of the mathematical decoder,
not a verification of the external Python parser or arithmetic runtime.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



















theorem recoh_mem_fast_candidates_iff
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (S : Finset G) :
    S ∈ recohFastCandidates U half recover ↔
      ∃ E : Finset G, E ⊆ U ∧ E.card = 3 ∧ (half (E.sum id)).isSome ∧
        recover (recohEdgeRepresentative half E) = S := by
  simp [recohFastCandidates, and_assoc]

theorem recoh_fast_candidates_card_three
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (hcard : ∀ B : Finset G, B.card = 3 → (recover B).card = 3)
    (S : Finset G) (hS : S ∈ recohFastCandidates U half recover) : S.card = 3 := by
  obtain ⟨E, _, hE, _, rfl⟩ := (recoh_mem_fast_candidates_iff U half recover S).mp hS
  apply hcard
  rw [recoh_edge_representative_card, hE]















section FiniteRefinement

variable [Fintype G]



/-- The fast decoder accepts exactly the three-element supports with
the supplied complete observation. -/
theorem recoh_mem_fast_decoder_iff {I : Type*}
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ))
    (hhalf : RecohHalfSolverSpec half)
    (hrecover : RecohTranslationRecoverySpec bank obs recover)
    (hU : recohSquareSupport obs.1 ⊆ U) (S : Finset G) :
    S ∈ recohFastDecoder U half recover bank obs ↔
      S.card = 3 ∧ recohObservation bank S = obs := by
  classical
  simp only [recohFastDecoder, Finset.mem_filter]
  constructor
  · rintro ⟨hS, hobs⟩
    exact ⟨recoh_fast_candidates_card_three U half recover hrecover.1 S hS, hobs⟩
  · rintro ⟨hS, hobs⟩
    exact ⟨recoh_fast_candidates_complete U half recover bank obs hhalf hrecover hU
      S hS hobs, hobs⟩

/-- Formal refinement: one representative plus recovery has exactly
the same result as the complete candidate specification. -/
theorem recoh_fast_decoder_eq_exact {I : Type*}
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ))
    (hhalf : RecohHalfSolverSpec half)
    (hrecover : RecohTranslationRecoverySpec bank obs recover)
    (hU : recohSquareSupport obs.1 ⊆ U) :
    recohFastDecoder U half recover bank obs = recohExactDecoder bank obs := by
  ext S
  rw [recoh_mem_fast_decoder_iff U half recover bank obs hhalf hrecover hU,
    recoh_mem_exact_decoder_iff]



end FiniteRefinement

variable {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2









/-- The sign-based one-representative decoder refines the exact decoder
for a bank with compatible, nonvanishing binary coordinates. -/
theorem p2m_local_recoh_sign_fast_decoder_eq_exact [Fintype G] {I : Type*}
    (U : Finset G) (half : G → Option G)
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ))
    (index : Fin r → I) (e : H₂ ≃+ (Fin r → ZMod 2))
    (hhalf : RecohHalfSolverSpec half)
    (hcoord : ∀ (u : H₂) (i : Fin r),
      bank (index i) (u : G) = if e u i = 0 then 1 else -1)
    (hnonzero : ∀ i (B : Finset G), B.card = 3 →
      recohSupportProbe (bank (index i)) B ≠ 0)
    (hU : recohSquareSupport obs.1 ⊆ U) :
    recohFastDecoder U half
      (recohSignRecoverSupport (fun i => bank (index i)) e (fun i => obs.2 (index i)))
      bank obs = recohExactDecoder bank obs := by
  exact recoh_fast_decoder_eq_exact U half _ bank obs hhalf
    (recoh_sign_recovery_spec bank obs index e hcoord hnonzero) hU

end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] {r : Nat}
  [inst_2 : Fintype.{p2m_u_0} G] {I : Type p2m_u_1} (U : Finset.{p2m_u_0} G) (half : G → Option.{p2m_u_0} G)
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (obs : Prod.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex)) (index : Fin r → I)
  (e :
    @AddEquiv.{p2m_u_0, 0}
      (@Subtype.{p2m_u_0 + 1} G fun x =>
        @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
            (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
            (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
            (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          x)
      (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
      (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
      (@Pi.instAdd.{0, 0} (Fin r) (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
        @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Semifield.toDivisionSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    Nat.fact_prime_two))))))),
  @Couret.STROBO2TORS.RecohHalfSolverSpec.{p2m_u_0} G inst half →
    (∀
        (u :
          @Subtype.{p2m_u_0 + 1} G fun x =>
            @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
              (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
              (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              x)
        (i : Fin r),
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
            (bank (index i))
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
              (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                (@AddEquiv.{p2m_u_0, 0}
                  (@Subtype.{p2m_u_0 + 1} G fun x =>
                    @Membership.mem.{p2m_u_0, p2m_u_0} G
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                      (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                        (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                      (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      x)
                  (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Pi.instAdd.{0, 0} (Fin r)
                    (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                    @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@DivisionSemiring.toSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Semifield.toDivisionSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                (fun x => Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@EquivLike.toFunLike.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                  (@AddEquiv.{p2m_u_0, 0}
                    (@Subtype.{p2m_u_0 + 1} G fun x =>
                      @Membership.mem.{p2m_u_0, p2m_u_0} G
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                          (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        x)
                    (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                      (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Pi.instAdd.{0, 0} (Fin r)
                      (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                      @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                  (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddEquiv.instEquivLike.{p2m_u_0, 0}
                    (@Subtype.{p2m_u_0 + 1} G fun x =>
                      @Membership.mem.{p2m_u_0, p2m_u_0} G
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                          (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        x)
                    (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                      (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Pi.instAdd.{0, 0} (Fin r)
                      (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                      @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@DivisionSemiring.toSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Semifield.toDivisionSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Field.toSemifield.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  Nat.fact_prime_two))))))))
                e u i)
              (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@instMulZeroClassOfSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@DivisionSemiring.toSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Semifield.toDivisionSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              Nat.fact_prime_two)))))))))
            (ZMod.decidableEq (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                (@AddEquiv.{p2m_u_0, 0}
                  (@Subtype.{p2m_u_0 + 1} G fun x =>
                    @Membership.mem.{p2m_u_0, p2m_u_0} G
                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                      (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                        (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                      (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      x)
                  (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                  (@Pi.instAdd.{0, 0} (Fin r)
                    (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                    @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@DivisionSemiring.toSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Semifield.toDivisionSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                (fun x => Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@EquivLike.toFunLike.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
                  (@AddEquiv.{p2m_u_0, 0}
                    (@Subtype.{p2m_u_0 + 1} G fun x =>
                      @Membership.mem.{p2m_u_0, p2m_u_0} G
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                          (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        x)
                    (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                      (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Pi.instAdd.{0, 0} (Fin r)
                      (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                      @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                  (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@AddEquiv.instEquivLike.{p2m_u_0, 0}
                    (@Subtype.{p2m_u_0 + 1} G fun x =>
                      @Membership.mem.{p2m_u_0, p2m_u_0} G
                        (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                        (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                          (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                          (@AddSubgroup.instSetLike.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                        (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                          (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        x)
                    (Fin r → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                      (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                        (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                    (@Pi.instAdd.{0, 0} (Fin r)
                      (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                      @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@DivisionSemiring.toSemiring.{0}
                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@Semifield.toDivisionSemiring.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (@Field.toSemifield.{0}
                                (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                  Nat.fact_prime_two))))))))
                e u i)
              (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@MulZeroClass.toZero.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (@instMulZeroClassOfSemiring.{0}
                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@DivisionSemiring.toSemiring.{0}
                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Semifield.toDivisionSemiring.{0}
                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                              Nat.fact_prime_two)))))))))
            (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
            (@Neg.neg.{0} Complex Complex.instNeg
              (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))))) →
      (∀ (i : Fin r) (B : Finset.{p2m_u_0} G),
          @Eq.{1} Nat (@Finset.card.{p2m_u_0} G B) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
            @Ne.{1} Complex (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank (index i)) B)
              (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero))) →
        @HasSubset.Subset.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instHasSubset.{p2m_u_0} G)
            (@Couret.STROBO2TORS.recohSquareSupport.{p2m_u_0} G inst_2
              (@Prod.fst.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex) obs))
            U →
          @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Couret.STROBO2TORS.recohFastDecoder.{p2m_u_0, p2m_u_1} G inst inst_1 I U half
              (@Couret.STROBO2TORS.recohSignRecoverSupport.{p2m_u_0} G inst inst_1 r (fun i => bank (index i)) e
                fun i => @Prod.snd.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex) obs (index i))
              bank obs)
            (@Couret.STROBO2TORS.recohExactDecoder.{p2m_u_0, p2m_u_1} G inst inst_1 inst_2 I bank obs) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_sign_fast_decoder_eq_exact

