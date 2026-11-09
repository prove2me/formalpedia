-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_sparse_backend_decoder_eq_exact
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:19.647981+00:00
-- url     : https://prove2.me/submissions/1bcb6304-5123-4b95-858d-b3fbaba12739

import Aesop
import Definitions.Def_Couret_RecohExactSignBackend_8d2941f5c2c9
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_checked_fast_decoder_eq_exact
import Theorems.Thm_Couret_STROBO2TORS_recoh_normalized_sparse_equal_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_recover_translation_coordinate
import Theorems.Thm_Couret_STROBO2TORS_recoh_sign_bit_from_bool_eq
import Theorems.Thm_Couret_STROBO2TORS_recoh_sign_recovery_spec
import Theorems.Thm_Couret_STROBO2TORS_recoh_sparse_observation_check_iff
import Definitions.Def_Couret_RecohFastDecoder_5bb89f11acce
import Definitions.Def_Couret_RecohCyclotomicNormalization_6797485e207c
import Definitions.Def_Couret_RecohSparseObservation_6dd9be0e8eb2

set_option autoImplicit false

/-!
Computable comparison bits and their refinement of complex sign recovery.

The comparison booleans are supplied by an exact arithmetic backend.  Only
their correctness proposition mentions complex numbers.  The recovered
coordinate vector and transport through a supplied coordinate equivalence
are ordinary Lean definitions, with no complex equality decision at runtime.
-/

namespace Couret.STROBO2TORS





variable {G : Type*} [AddCommGroup G] {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2



@[simp] theorem recoh_recover_translation_from_bools_coordinate
    (e : H₂ ≃+ (Fin r → ZMod 2)) (same : Fin r → Bool) (i : Fin r) :
    e (recohRecoverTranslationFromBools e same) i = recohSignBitFromBool (same i) := by
  simp [recohRecoverTranslationFromBools]

theorem recoh_boolean_recovery_refines_complex
    (e : H₂ ≃+ (Fin r → ZMod 2)) (base obs : Fin r → ℂ)
    (same : Fin r → Bool) (h : ∀ i, same i = true ↔ obs i = base i) :
    recohRecoverTranslationFromBools e same = recohRecoverTranslation e base obs := by
  apply e.injective
  funext i
  rw [recoh_recover_translation_from_bools_coordinate,
    recoh_recover_translation_coordinate]
  exact recoh_sign_bit_from_bool_eq (base i) (obs i) (same i) (h i)

variable [DecidableEq G]







theorem recoh_primary_sign_bools_exact (k : Fin r → ℕ)
    (base obs : Fin r → List ℕ) (ζ : Fin r → ℂ)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) (2 ^ (k i + 1))) (i : Fin r) :
    recohPrimarySignBools k base obs i = true ↔
      ((obs i).map ((ζ i) ^ ·)).sum = ((base i).map ((ζ i) ^ ·)).sum :=
  recoh_normalized_sparse_equal_iff Nat.prime_two (k i) (hζ i) (obs i) (base i)





theorem recoh_boolean_recover_support_eq_sign
    (bank : Fin r → AddChar G ℂ) (e : H₂ ≃+ (Fin r → ZMod 2))
    (obs : Fin r → ℂ) (same : Finset G → Fin r → Bool)
    (hsame : ∀ B i, same B i = true ↔ obs i = recohSupportProbe (bank i) B)
    (B : Finset G) :
    recohBooleanRecoverSupport e same B = recohSignRecoverSupport bank e obs B := by
  unfold recohBooleanRecoverSupport recohSignRecoverSupport
  rw [recoh_boolean_recovery_refines_complex e _ obs (same B) (hsame B)]

theorem recoh_boolean_recovery_spec {I : Type*}
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ))
    (index : Fin r → I) (e : H₂ ≃+ (Fin r → ZMod 2))
    (same : Finset G → Fin r → Bool)
    (hcoord : ∀ (u : H₂) (i : Fin r),
      bank (index i) (u : G) = if e u i = 0 then 1 else -1)
    (hnonzero : ∀ i (B : Finset G), B.card = 3 →
      recohSupportProbe (bank (index i)) B ≠ 0)
    (hsame : ∀ B i, same B i = true ↔ obs.2 (index i) =
      recohSupportProbe (bank (index i)) B) :
    RecohTranslationRecoverySpec bank obs (recohBooleanRecoverSupport e same) := by
  have heq : recohBooleanRecoverSupport e same =
      recohSignRecoverSupport (fun i => bank (index i)) e (fun i => obs.2 (index i)) := by
    funext B
    exact recoh_boolean_recover_support_eq_sign _ e _ same hsame B
  rw [heq]
  exact recoh_sign_recovery_spec bank obs index e hcoord hnonzero



theorem recoh_sparse_recovery_spec {I : Type*}
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ))
    (index : Fin r → I) (e : H₂ ≃+ (Fin r → ZMod 2))
    (k : Fin r → ℕ) (encode : Fin r → Finset G → List ℕ)
    (obsExp : Fin r → List ℕ) (ζ : Fin r → ℂ)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) (2 ^ (k i + 1)))
    (hencode : ∀ i B, ((encode i B).map ((ζ i) ^ ·)).sum =
      recohSupportProbe (bank (index i)) B)
    (hobs : ∀ i, ((obsExp i).map ((ζ i) ^ ·)).sum = obs.2 (index i))
    (hcoord : ∀ (u : H₂) (i : Fin r),
      bank (index i) (u : G) = if e u i = 0 then 1 else -1)
    (hnonzero : ∀ i (B : Finset G), B.card = 3 →
      recohSupportProbe (bank (index i)) B ≠ 0) :
    RecohTranslationRecoverySpec bank obs
      (recohSparseRecoverSupport e k encode obsExp) := by
  apply recoh_boolean_recovery_spec bank obs index e _ hcoord hnonzero
  intro B i
  rw [recoh_primary_sign_bools_exact k _ obsExp ζ hζ i, hencode, hobs]

/-- The executable sparse sign recovery and any verified Boolean observation
checker refine the complete mathematical decoder. -/
theorem recoh_sparse_sign_checked_decoder_eq_exact [Fintype G] {I : Type*}
    (U : Finset G) (half : G → Option G)
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ))
    (index : Fin r → I) (e : H₂ ≃+ (Fin r → ZMod 2))
    (k : Fin r → ℕ) (encode : Fin r → Finset G → List ℕ)
    (obsExp : Fin r → List ℕ) (ζ : Fin r → ℂ)
    (check : Finset G → Bool)
    (hhalf : RecohHalfSolverSpec half)
    (hU : recohSquareSupport obs.1 ⊆ U)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) (2 ^ (k i + 1)))
    (hencode : ∀ i B, ((encode i B).map ((ζ i) ^ ·)).sum =
      recohSupportProbe (bank (index i)) B)
    (hobs : ∀ i, ((obsExp i).map ((ζ i) ^ ·)).sum = obs.2 (index i))
    (hcoord : ∀ (u : H₂) (i : Fin r),
      bank (index i) (u : G) = if e u i = 0 then 1 else -1)
    (hnonzero : ∀ i (B : Finset G), B.card = 3 →
      recohSupportProbe (bank (index i)) B ≠ 0)
    (hcheck : ∀ S : Finset G, check S = true ↔ recohObservation bank S = obs) :
    recohCheckedFastDecoder U half (recohSparseRecoverSupport e k encode obsExp) check =
      recohExactDecoder bank obs := by
  exact recoh_checked_fast_decoder_eq_exact U half _ check bank obs hhalf
    (recoh_sparse_recovery_spec bank obs index e k encode obsExp ζ hζ hencode hobs
      hcoord hnonzero) hU hcheck



/-- Complete refinement with the concrete sparse checker.  The hypotheses
describe the supplied coordinates, primary encodings and support coverage;
the Boolean recovery and checking contracts are proved, not assumed here. -/
theorem p2m_local_recoh_sparse_backend_decoder_eq_exact [Fintype G] {m : ℕ}
    (U : Finset G) (R : G → ℕ) (half : G → Option G)
    (bank : Fin m → AddChar G ℂ) (obs : Fin m → ℂ)
    (index : Fin r → Fin m) (e : H₂ ≃+ (Fin r → ZMod 2))
    (k2 : Fin r → ℕ) (enc2 : Fin r → Finset G → List ℕ)
    (obs2 : Fin r → List ℕ) (ζ2 : Fin r → ℂ)
    (p k : Fin m → ℕ) (enc : Fin m → Finset G → List ℕ)
    (obsExp : Fin m → List ℕ) (ζ : Fin m → ℂ)
    (hhalf : RecohHalfSolverSpec half)
    (hR : ∀ z, R z ≠ 0 → z ∈ U)
    (hζ2 : ∀ i, IsPrimitiveRoot (ζ2 i) (2 ^ (k2 i + 1)))
    (henc2 : ∀ i B, ((enc2 i B).map ((ζ2 i) ^ ·)).sum =
      recohSupportProbe (bank (index i)) B)
    (hobs2 : ∀ i, ((obs2 i).map ((ζ2 i) ^ ·)).sum = obs (index i))
    (hcoord : ∀ (u : H₂) (i : Fin r),
      bank (index i) (u : G) = if e u i = 0 then 1 else -1)
    (hnonzero : ∀ i (B : Finset G), B.card = 3 →
      recohSupportProbe (bank (index i)) B ≠ 0)
    (hp : ∀ i, (p i).Prime)
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) ((p i) ^ (k i + 1)))
    (henc : ∀ i B, ((enc i B).map ((ζ i) ^ ·)).sum = recohSupportProbe (bank i) B)
    (hobs : ∀ i, ((obsExp i).map ((ζ i) ^ ·)).sum = obs i) :
    recohSparseBackendDecoder U R half e k2 enc2 obs2 p k enc obsExp =
      recohExactDecoder bank (R, obs) := by
  apply recoh_sparse_sign_checked_decoder_eq_exact U half bank (R, obs) index e
    k2 enc2 obs2 ζ2 _ hhalf
  · intro z hz
    exact hR z (Nat.ne_of_gt (by simpa only [recoh_mem_square_support] using hz))
  · exact hζ2
  · exact henc2
  · exact hobs2
  · exact hcoord
  · exact hnonzero
  · intro S
    exact recoh_sparse_observation_check_iff U R p k enc obsExp S bank ζ obs
      hR hp hζ (fun i => henc i S) hobs



end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] {r : Nat} [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] {m : Nat} (U : Finset.{p2m_u_0} G) (R : G → Nat) (half : G → Option.{p2m_u_0} G)
  (bank :
    Fin m →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (obs : Fin m → Complex) (index : Fin r → Fin m)
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
                    Nat.fact_prime_two)))))))
  (k2 : Fin r → Nat) (enc2 : Fin r → Finset.{p2m_u_0} G → List.{0} Nat) (obs2 : Fin r → List.{0} Nat)
  (ζ2 : Fin r → Complex) (p k : Fin m → Nat) (enc : Fin m → Finset.{p2m_u_0} G → List.{0} Nat)
  (obsExp : Fin m → List.{0} Nat) (ζ : Fin m → Complex),
  @Couret.STROBO2TORS.RecohHalfSolverSpec.{p2m_u_0} G inst half →
    (∀ (z : G),
        @Ne.{1} Nat (R z) (@OfNat.ofNat.{0} Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) →
          @Membership.mem.{p2m_u_0, p2m_u_0} G (Finset.{p2m_u_0} G)
            (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) G (@Finset.instSetLike.{p2m_u_0} G)) U z) →
      (∀ (i : Fin r),
          @IsPrimitiveRoot.{0} Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing) (ζ2 i)
            (@HPow.hPow.{0, 0, 0} Nat Nat Nat (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid))
              (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
              (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (k2 i)
                (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
        (∀ (i : Fin r) (B : Finset.{p2m_u_0} G),
            @Eq.{1} Complex
              (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                (@List.map.{0, 0} Nat Complex
                  (fun x =>
                    @HPow.hPow.{0, 0, 0} Complex Nat Complex
                      (@instHPow.{0, 0} Complex Nat
                        (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                      (ζ2 i) x)
                  (enc2 i B)))
              (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank (index i)) B)) →
          (∀ (i : Fin r),
              @Eq.{1} Complex
                (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                  (@List.map.{0, 0} Nat Complex
                    (fun x =>
                      @HPow.hPow.{0, 0, 0} Complex Nat Complex
                        (@instHPow.{0, 0} Complex Nat
                          (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                        (ζ2 i) x)
                    (obs2 i)))
                (obs (index i))) →
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
                                  (@Field.toSemifield.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
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
                                  (@Field.toSemifield.{0}
                                    (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (@ZMod.instField (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                                      Nat.fact_prime_two)))))))))
                    (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))
                    (@Neg.neg.{0} Complex Complex.instNeg
                      (@OfNat.ofNat.{0} Complex (nat_lit 1) (@One.toOfNat1.{0} Complex Complex.instOne))))) →
              (∀ (i : Fin r) (B : Finset.{p2m_u_0} G),
                  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G B)
                      (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
                    @Ne.{1} Complex (@Couret.STROBO2TORS.recohSupportProbe.{p2m_u_0} G inst (bank (index i)) B)
                      (@OfNat.ofNat.{0} Complex (nat_lit 0) (@Zero.toOfNat0.{0} Complex Complex.instZero))) →
                (∀ (i : Fin m), Nat.Prime (p i)) →
                  (∀ (i : Fin m),
                      @IsPrimitiveRoot.{0} Complex (@CommRing.toCommMonoid.{0} Complex Complex.commRing) (ζ i)
                        (@HPow.hPow.{0, 0, 0} Nat Nat Nat
                          (@instHPow.{0, 0} Nat Nat (@Monoid.toPow.{0} Nat Nat.instMonoid)) (p i)
                          (@HAdd.hAdd.{0, 0, 0} Nat Nat Nat (@instHAdd.{0} Nat instAddNat) (k i)
                            (@OfNat.ofNat.{0} Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))))) →
                    (∀ (i : Fin m) (B : Finset.{p2m_u_0} G),
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
                      (∀ (i : Fin m),
                          @Eq.{1} Complex
                            (@List.sum.{0} Complex Complex.instAdd Complex.instZero
                              (@List.map.{0, 0} Nat Complex
                                (fun x =>
                                  @HPow.hPow.{0, 0, 0} Complex Nat Complex
                                    (@instHPow.{0, 0} Complex Nat
                                      (@Monoid.toPow.{0} Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring)))
                                    (ζ i) x)
                                (obsExp i)))
                            (obs i)) →
                        @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                          (@Couret.STROBO2TORS.recohSparseBackendDecoder.{p2m_u_0} G inst r inst_1 m U R half e k2 enc2
                            obs2 p k enc obsExp)
                          (@Couret.STROBO2TORS.recohExactDecoder.{p2m_u_0, 0} G inst inst_1 inst_2 (Fin m) bank
                            (@Prod.mk.{p2m_u_0, 0} (G → Nat) (Fin m → Complex) R obs)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_sparse_backend_decoder_eq_exact

