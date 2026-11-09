-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_early_coefficient_backend_decoder_eq_backend
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:11.190349+00:00
-- url     : https://prove2.me/submissions/79283406-8306-4e98-8b4e-abbfe5d71e9f

import Aesop
import Definitions.Def_Couret_RecohEarlySignChecks_6186d05e32eb
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
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_readings_check_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_early_readings_of_translated_observation
import Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_recover_support_square
import Theorems.Thm_Couret_STROBO2TORS_recoh_prepared_fast_decoder_eq_checked
import Definitions.Def_Couret_RecohPreparedDecoder_2b97e051dec5

set_option autoImplicit false

/-!
Early rejection of incompatible binary and ternary readings.

The bank index is J ⊕ K.  The intended cyclic bank uses prime two on J and
prime three on K.  The executable tests retain the supplied prime parameters;
their correctness uses explicit primary-representation contracts and the two
roles on G[2]: signs on J, trivial character values on K.

Binary observations must equal the representative reading or its negative;
ternary observations must equal the representative reading.  These are exact
integer-coefficient comparisons.  A final accepted recovered support always
passes these early tests, without nonvanishing or cardinality assumptions.
Combining them with the early square check therefore preserves the answer of
the full coefficient backend.  This proves an order of typed mathematical
operations, not the external Python parser, cache, or runtime.
-/

namespace Couret.STROBO2TORS

variable {G J K : Type*} [AddCommGroup G] [DecidableEq G]
variable [Fintype J] [Fintype K]

local notation "H₂" => recohTorsionSubgroup (G := G) 2







/-- Final acceptance after any indexed recovery implies that the early
reading test accepts the original representative.  The equality-bit function
may be arbitrary: neither its correctness nor nonvanishing is needed here. -/
theorem recoh_early_readings_of_final_check
    (U : Finset G) (R : G → ℕ)
    (p k : J ⊕ K → ℕ) (enc : J ⊕ K → Finset G → List ℕ)
    (obsTerms : J ⊕ K → RecohSparseTerms)
    (bank : J ⊕ K → AddChar G ℂ) (ζ obs : J ⊕ K → ℂ)
    (e : H₂ ≃+ (J → ZMod 2)) (same : Finset G → J → Bool)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hred : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (henc : ∀ i S, ((enc i S).map ((ζ i) ^ ·)).sum = recohSupportProbe (bank i) S)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i)
    (hcoord : ∀ (u : H₂) (j : J),
      bank (Sum.inl j) (u : G) = if e u j = 0 then 1 else -1)
    (hternary : ∀ (u : H₂) (j : K), bank (Sum.inr j) (u : G) = 1)
    (B : Finset G)
    (hfinal : recohCoefficientObservationCheck U R p k enc obsTerms
      (recohIndexedRecoverSupport e same B) = true) :
    recohEarlyReadingsCheck p k enc obsTerms B = true := by
  rw [recohCoefficientObservationCheck, Bool.and_eq_true] at hfinal
  have hreadings := (recoh_coefficient_readings_check_iff p k enc obsTerms
    (recohIndexedRecoverSupport e same B) bank ζ obs hp hζ hred
    (fun i => henc i _) hobs).mp hfinal.2
  apply recoh_early_readings_of_translated_observation p k enc obsTerms bank ζ obs e
    hp hζ hred B (fun i => henc i B) hobs hcoord hternary
    (recohIndexedRecoverTranslation e (same B))
  intro i
  exact congrFun hreadings i





/-- The early-rejection control flow accepts exactly the same supports
as the full coefficient backend.  The role contracts, rather than a
nonvanishing hypothesis, justify these necessary early conditions. -/
theorem p2m_local_recoh_early_coefficient_backend_decoder_eq_backend
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (e : H₂ ≃+ (J → ZMod 2)) (p k : J ⊕ K → ℕ)
    (enc : J ⊕ K → Finset G → List ℕ) (obsTerms : J ⊕ K → RecohSparseTerms)
    (bank : J ⊕ K → AddChar G ℂ) (ζ obs : J ⊕ K → ℂ)
    (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hred : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (henc : ∀ i S, ((enc i S).map ((ζ i) ^ ·)).sum = recohSupportProbe (bank i) S)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i)
    (hcoord : ∀ (u : H₂) (j : J),
      bank (Sum.inl j) (u : G) = if e u j = 0 then 1 else -1)
    (hternary : ∀ (u : H₂) (j : K), bank (Sum.inr j) (u : G) = 1) :
    recohEarlyCoefficientBackendDecoder U R half e p k enc obsTerms =
      recohCoefficientBackendDecoder U R half Sum.inl e p k enc obsTerms := by
  apply recoh_prepared_fast_decoder_eq_checked
  intro B hB
  rw [recohEarlyCandidateCheck, Bool.and_eq_true]
  constructor
  · have hsquare := hB
    rw [recohCoefficientObservationCheck, Bool.and_eq_true] at hsquare
    apply (recoh_sparse_square_check_iff U B R hR).mpr
    exact (recoh_indexed_recover_support_square e _ B).symm.trans
      ((recoh_sparse_square_check_iff U _ R hR).mp hsquare.1)
  · exact recoh_early_readings_of_final_check U R p k enc obsTerms bank ζ obs e _
      hp hζ hred henc hobs hcoord hternary B hB



end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {G : Type p2m_u_0} {J : Type p2m_u_1} {K : Type p2m_u_2} [inst : AddCommGroup.{p2m_u_0} G]
  [inst_1 : DecidableEq.{p2m_u_0 + 1} G] [inst_2 : Fintype.{p2m_u_1} J] [inst_3 : Fintype.{p2m_u_2} K]
  (U : Finset.{p2m_u_0} G) (R : G → Nat) (half : G → Option.{p2m_u_0} G)
  (e :
    @AddEquiv.{p2m_u_0, p2m_u_1}
      (@Subtype.{p2m_u_0 + 1} G fun x =>
        @Membership.mem.{p2m_u_0, p2m_u_0} G (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
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
      (@Pi.instAdd.{p2m_u_1, 0} J (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
        @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Semifield.toDivisionSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    Nat.fact_prime_two)))))))
  (p k : Sum.{p2m_u_1, p2m_u_2} J K → Nat) (enc : Sum.{p2m_u_1, p2m_u_2} J K → Finset.{p2m_u_0} G → List.{0} Nat)
  (obsTerms : Sum.{p2m_u_1, p2m_u_2} J K → Couret.STROBO2TORS.RecohSparseTerms)
  (bank :
    Sum.{p2m_u_1, p2m_u_2} J K →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (ζ obs : Sum.{p2m_u_1, p2m_u_2} J K → Complex),
  (∀ (z : G),
      @Ne.{1} Nat (R z) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
        @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
          (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) U z) →
    (∀ (i : Sum.{p2m_u_1, p2m_u_2} J K), Nat.Prime (p i)) →
      (∀ (i : Sum.{p2m_u_1, p2m_u_2} J K),
          @IsPrimitiveRoot.{0} Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing) (ζ i)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) (p i)
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (k i)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        (∀ (i : Sum.{p2m_u_1, p2m_u_2} J K), Couret.STROBO2TORS.RecohCoefficientsReduced (p i) (k i) (obsTerms i)) →
          (∀ (i : Sum.{p2m_u_1, p2m_u_2} J K) (S : Finset.{p2m_u_0} G),
              @Eq.{1} Complex
                (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                  (@List.map.{0, 0} Nat Complex
                    (fun x =>
                      @HPow.hPow.{0, 0, 0} Complex Nat Complex
                        (@instHPow.{0, 0} Complex Nat
                          (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                        (ζ i) x)
                    (enc i S)))
                (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) S)) →
            (∀ (i : Sum.{p2m_u_1, p2m_u_2} J K),
                @Eq.{1} Complex (Couret.STROBO2TORS.recohCoefficientValue (ζ i) (obsTerms i)) (obs i)) →
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
                      (bank (@Sum.inl.{p2m_u_1, p2m_u_2} J K j))
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
                        (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (nat_lit 0)
                          (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@MulZeroClass.toZero.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                        (@OfNat.ofNat.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (nat_lit 0)
                          (@Zero.toOfNat0.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (@MulZeroClass.toZero.{0}
                              (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                    (j : K),
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
                        (bank (@Sum.inr.{p2m_u_1, p2m_u_2} J K j))
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
                      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))) →
                  @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                    (@Couret.STROBO2TORS.recohEarlyCoefficientBackendDecoder.{p2m_u_0, p2m_u_1, p2m_u_2} G J K inst
                      inst_1 inst_2 inst_3 U R half e p k enc obsTerms)
                    (@Couret.STROBO2TORS.recohCoefficientBackendDecoder.{p2m_u_0, max p2m_u_2 p2m_u_1, p2m_u_1} G
                      (Sum.{p2m_u_1, p2m_u_2} J K) J inst inst_1 (@instFintypeSum.{p2m_u_1, p2m_u_2} J K inst_2 inst_3)
                      U R half (@Sum.inl.{p2m_u_1, p2m_u_2} J K) e p k enc obsTerms) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_early_coefficient_backend_decoder_eq_backend

