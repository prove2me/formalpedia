-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_coefficient_backend_decoder_eq_exact
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:02:41.284381+00:00
-- url     : https://prove2.me/submissions/14f63088-c0e6-473e-bb40-514457897818

import Aesop
import Definitions.Def_Couret_RecohCoefficientDecoder_a5265698d3d8
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_observation_check_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_coefficient_sign_bools_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_indexed_checked_decoder_eq_exact
import Definitions.Def_Couret_RecohIndexedSignRecovery_d641979954b3
import Definitions.Def_Couret_RecohCoefficientObservations_4ffca285ab72

set_option autoImplicit false

/-!
The RECOH decoder with observed coefficients in the cyclotomic power basis.

The observed inputs are finite lists of exponent/integer-coefficient pairs,
as used by the Python observation format.  Candidate readings are generated
from root exponents and compared directly to those pairs.  No inverse map
from a coefficient polynomial to a list of roots is required.

The binary probes are selected inside the same full bank and use the same
observed inputs.  Their index type is arbitrary, allowing the actual subtype
of even cyclic coordinates rather than a noncomputable reindexing to Fin r.
-/

namespace Couret.STROBO2TORS

variable {G I J : Type*} [AddCommGroup G] [DecidableEq G]

local notation "H₂" => recohTorsionSubgroup (G := G) 2





variable [Fintype I]



/-- The observed coefficients have their ordinary polynomial value.  Under
the explicit representation contracts, the backend is the exact decoder. -/
theorem p2m_local_recoh_coefficient_backend_decoder_eq_exact [Fintype G]
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
    recohCoefficientBackendDecoder U R half index e p k enc obsTerms =
      recohExactDecoder bank (R, obs) := by
  apply recoh_indexed_checked_decoder_eq_exact U half bank (R, obs) index e _ _
    hhalf
  · intro z hz
    exact hR z (Nat.ne_of_gt (by simpa only [recoh_mem_square_support] using hz))
  · exact hcoord
  · exact hnonzero
  · intro B j
    exact recoh_coefficient_sign_bools_exact index p k enc obsTerms bank ζ obs
      hp hζ hred henc hobs B j
  · intro S
    exact recoh_coefficient_observation_check_iff U R p k enc obsTerms S bank ζ obs
      hR hp hζ hred (fun i => henc i S) hobs



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
                      (@Couret.STROBO2TORS.recohCoefficientBackendDecoder.{p2m_u_0, p2m_u_1, p2m_u_2} G I J inst inst_1
                        inst_2 U R half index e p k enc obsTerms)
                      (@Couret.STROBO2TORS.recohExactDecoder.{p2m_u_0, p2m_u_1} G inst inst_1 inst_3 I bank
                        (@Prod.mk.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex) R obs)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_coefficient_backend_decoder_eq_exact

