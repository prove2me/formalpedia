-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_parity_coefficient_backend_eq_exact
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:58:32.773846+00:00
-- url     : https://prove2.me/submissions/a7227d5f-0eda-4003-9fd1-5b7a2b6876d8

import Aesop
import Definitions.Def_Couret_RecohParityDecoder_e5701300ff06
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finiteness
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_observation_check_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_sign_bools_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_boolean_recovery_spec
import Theorems.Thm_Couret_STROBO2TORS_recoh_representative_checked_decoder_eq_exact
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
import Definitions.Def_Couret_RecohParityOrbitRefinement_49bc5e3f0a8c
import Definitions.Def_Couret_RecohParitySelector_0eb69704c517

set_option autoImplicit false

/-!
Coefficient decoding from the compact parity family.

The generic bridge uses a proved cover modulo two-torsion, the historical
sign-recovery specification and the exact integer observation checker.
The new candidate construction is an image of the parity family, not the
historical edge-triple enumeration. Definitions enumerate neither G nor
its two-torsion subgroup. Complex values occur only in the specification.
-/

namespace Couret.STROBO2TORS

variable {G I J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2













variable [Fintype I]





/-- All generic recovery and checking obligations are discharged by the
existing coefficient lemmas. Only the displayed mathematical data contracts
remain; in the cyclic instance below they are constructed from q. -/
theorem p2m_local_recoh_parity_coefficient_backend_eq_exact [Fintype G]
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (index : J → I) (e : H₂ ≃+ (J → ZMod 2))
    (p k : I → ℕ) (enc : I → Finset G → List ℕ)
    (obsTerms : I → RecohSparseTerms)
    (bank : I → AddChar G ℂ) (ζ obs : I → ℂ)
    (hhalf : RecohHalfSolverSpec half)
    (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (hred : ∀ i, RecohCoefficientsReduced (p i) (k i) (obsTerms i))
    (henc : ∀ i B, ((enc i B).map ((ζ i) ^ ·)).sum = recohSupportProbe (bank i) B)
    (hobs : ∀ i, recohCoefficientValue (ζ i) (obsTerms i) = obs i)
    (hcoord : ∀ (u : H₂) (j : J),
      bank (index j) (u : G) = if e u j = 0 then 1 else -1)
    (hnonzero : ∀ j (B : Finset G), B.card = 3 →
      recohSupportProbe (bank (index j)) B ≠ 0) :
    recohParityCoefficientBackendDecoder U R half index e p k enc obsTerms =
      recohExactDecoder bank (R, obs) := by
  apply recoh_representative_checked_decoder_eq_exact
    (recohParityRepresentatives U R half)
    (recohIndexedRecoverSupport e (recohCoefficientSignBools index p k enc obsTerms))
    (recohCoefficientObservationCheck U R p k enc obsTerms) bank (R, obs)
  · exact recoh_parity_representatives_cover U R half hhalf hR
  · apply recoh_indexed_boolean_recovery_spec bank (R, obs) index e _ hcoord hnonzero
    intro B j
    exact recoh_coefficient_sign_bools_exact index p k enc obsTerms bank ζ obs
      hp hζ hred henc hobs B j
  · intro S
    exact recoh_coefficient_observation_check_iff U R p k enc obsTerms S bank ζ obs
      hR hp hζ hred (fun i => henc i S) hobs

section CyclicSelected

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





































































end CyclicSelected

end Couret.STROBO2TORS

universe p2m_u_0 p2m_u_1 p2m_u_2
theorem solution : ∀ {G : Type p2m_u_0} {I : Type p2m_u_1} {J : Type p2m_u_2} [inst : AddCommGroup.{p2m_u_0} G]
  [inst_1 : DecidableEq.{p2m_u_0 + 1} G] [inst_2 : Fintype.{p2m_u_1} I] [inst_3 : Fintype.{p2m_u_0} G]
  (U : Finset.{p2m_u_0} G) (R : G → Nat) (half : G → Option.{p2m_u_0} G) (index : J → I)
  (e :
    @AddEquiv.{p2m_u_0, p2m_u_2}
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
      (@Pi.instAdd.{p2m_u_2, 0} J (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
        @Distrib.toAdd.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (@instDistribOfSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@DivisionSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Semifield.toDivisionSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (@Field.toSemifield.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                    Nat.fact_prime_two)))))))
  (p k : I → Nat) (enc : I → Finset.{p2m_u_0} G → List.{0} Nat) (obsTerms : I → Couret.STROBO2TORS.RecohSparseTerms)
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (ζ obs : I → Complex),
  @Couret.STROBO2TORS.RecohHalfSolverSpec.{p2m_u_0} G inst half →
    (∀ (z : G),
        @Ne.{1} Nat (R z) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) U z) →
      (∀ (i : I), Nat.Prime (p i)) →
        (∀ (i : I),
            @IsPrimitiveRoot.{0} Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing) (ζ i)
              (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) (p i)
                (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (k i)
                  (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
          (∀ (i : I), Couret.STROBO2TORS.RecohCoefficientsReduced (p i) (k i) (obsTerms i)) →
            (∀ (i : I) (B : Finset.{p2m_u_0} G),
                @Eq.{1} Complex
                  (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                    (@List.map.{0, 0} Nat Complex
                      (fun x =>
                        @HPow.hPow.{0, 0, 0} Complex Nat Complex
                          (@instHPow.{0, 0} Complex Nat
                            (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                          (ζ i) x)
                      (enc i B)))
                  (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank i) B)) →
              (∀ (i : I), @Eq.{1} Complex (Couret.STROBO2TORS.recohCoefficientValue (ζ i) (obsTerms i)) (obs i)) →
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
                          (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_2 + 1), p2m_u_0 + 1, p2m_u_2 + 1}
                            (@AddEquiv.{p2m_u_0, p2m_u_2}
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
                              (@Pi.instAdd.{p2m_u_2, 0} J
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
                            (@EquivLike.toFunLike.{max (p2m_u_0 + 1) (p2m_u_2 + 1), p2m_u_0 + 1, p2m_u_2 + 1}
                              (@AddEquiv.{p2m_u_0, p2m_u_2}
                                (@Subtype.{p2m_u_0 + 1} G fun x =>
                                  @Membership.mem.{p2m_u_0, p2m_u_0} G
                                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                                      (@AddSubgroup.instSetLike.{p2m_u_0} G
                                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    x)
                                (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                                  (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (@Pi.instAdd.{p2m_u_2, 0} J
                                  (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                                  @Distrib.toAdd.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@instDistribOfSemiring.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@DivisionSemiring.toSemiring.{0}
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (@Semifield.toDivisionSemiring.{0}
                                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (@Field.toSemifield.{0}
                                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (@ZMod.instField
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
                              (@AddEquiv.instEquivLike.{p2m_u_0, p2m_u_2}
                                (@Subtype.{p2m_u_0 + 1} G fun x =>
                                  @Membership.mem.{p2m_u_0, p2m_u_0} G
                                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                                      (@AddSubgroup.instSetLike.{p2m_u_0} G
                                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    x)
                                (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                                  (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (@Pi.instAdd.{p2m_u_2, 0} J
                                  (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                                  @Distrib.toAdd.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@instDistribOfSemiring.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@DivisionSemiring.toSemiring.{0}
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (@Semifield.toDivisionSemiring.{0}
                                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (@Field.toSemifield.{0}
                                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (@ZMod.instField
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
                          (@DFunLike.coe.{max (p2m_u_0 + 1) (p2m_u_2 + 1), p2m_u_0 + 1, p2m_u_2 + 1}
                            (@AddEquiv.{p2m_u_0, p2m_u_2}
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
                              (@Pi.instAdd.{p2m_u_2, 0} J
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
                            (@EquivLike.toFunLike.{max (p2m_u_0 + 1) (p2m_u_2 + 1), p2m_u_0 + 1, p2m_u_2 + 1}
                              (@AddEquiv.{p2m_u_0, p2m_u_2}
                                (@Subtype.{p2m_u_0 + 1} G fun x =>
                                  @Membership.mem.{p2m_u_0, p2m_u_0} G
                                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                                      (@AddSubgroup.instSetLike.{p2m_u_0} G
                                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    x)
                                (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                                  (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (@Pi.instAdd.{p2m_u_2, 0} J
                                  (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                                  @Distrib.toAdd.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@instDistribOfSemiring.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@DivisionSemiring.toSemiring.{0}
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (@Semifield.toDivisionSemiring.{0}
                                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (@Field.toSemifield.{0}
                                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (@ZMod.instField
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
                              (@AddEquiv.instEquivLike.{p2m_u_0, p2m_u_2}
                                (@Subtype.{p2m_u_0 + 1} G fun x =>
                                  @Membership.mem.{p2m_u_0, p2m_u_0} G
                                    (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst))
                                    (@SetLike.instMembership.{p2m_u_0, p2m_u_0}
                                      (@AddSubgroup.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)) G
                                      (@AddSubgroup.instSetLike.{p2m_u_0} G
                                        (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
                                    (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                                      (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    x)
                                (J → ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (@AddSubgroup.add.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)
                                  (@Couret.STROBO2TORS.recohTorsionSubgroup.{p2m_u_0} G inst
                                    (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))
                                (@Pi.instAdd.{p2m_u_2, 0} J
                                  (fun a => ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) fun i =>
                                  @Distrib.toAdd.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@instDistribOfSemiring.{0}
                                      (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (@DivisionSemiring.toSemiring.{0}
                                        (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (@Semifield.toDivisionSemiring.{0}
                                          (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                          (@Field.toSemifield.{0}
                                            (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                            (@ZMod.instField
                                              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
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
                  (∀ (j : J) (B : Finset.{p2m_u_0} G),
                      @Eq.{1} Nat (@Finset.card.{p2m_u_0} G B)
                          (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                        @Ne.{1} Complex (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank (index j)) B)
                          (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero))) →
                    @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                      (@Couret.STROBO2TORS.recohParityCoefficientBackendDecoder.{p2m_u_0, p2m_u_1, p2m_u_2} G I J inst
                        inst_1 inst_2 U R half index e p k enc obsTerms)
                      (@Couret.STROBO2TORS.recohExactDecoder.{p2m_u_0, p2m_u_1} G inst inst_1 inst_3 I bank
                        (@Prod.mk.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex) R obs)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_parity_coefficient_backend_eq_exact

