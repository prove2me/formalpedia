-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_parity_selected_observation_check_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:28:25.974624+00:00
-- url     : https://prove2.me/submissions/fb42c1db-0bea-4115-b9a0-2930f814d967

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_bank_encoding_interpret
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_bank_prime
import Theorems.Thm_Couret_STROBO2TORS_recoh_selected_bank_root_primitive
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







section CyclicSelected

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]







































/-- The actual selected integer checker recognizes the full mathematical
observation, independently of which representative family was decoded. -/
theorem p2m_local_recoh_parity_selected_observation_check_iff
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (hred : ∀ i, RecohCoefficientsReduced
      (recohParitySelectedBankPrime q entries i)
      (recohParitySelectedBankDepth q entries i) (terms i))
    (S : Finset ((i : Fin d) → ZMod (q i))) :
    recohCoefficientObservationCheck (recohSelectedSquareSupport q entries)
      (recohTypedSquareValue entries) (recohParitySelectedBankPrime q entries)
      (recohParitySelectedBankDepth q entries)
      (recohParitySelectedBankEncoding q entries) terms S = true ↔
        recohObservation (recohParitySelectedObservedBank q entries) S =
          recohParitySelectedTypedObservation q entries terms := by
  apply recoh_coefficient_observation_check_iff
    (recohSelectedSquareSupport q entries) (recohTypedSquareValue entries)
    (recohParitySelectedBankPrime q entries) (recohParitySelectedBankDepth q entries)
    (recohParitySelectedBankEncoding q entries) terms S
    (recohParitySelectedObservedBank q entries) (recohParitySelectedBankRoot q entries)
    (fun i => recohCoefficientValue (recohParitySelectedBankRoot q entries i) (terms i))
  · exact recoh_selected_square_support_covered q entries
  · intro i
    exact recoh_selected_bank_prime q entries (recohParitySelectedBankEquiv q entries i)
  · intro i
    exact recoh_selected_bank_root_primitive q entries (recohParitySelectedBankEquiv q entries i)
  · exact hred
  · intro i
    exact recoh_selected_bank_encoding_interpret q entries
      (recohParitySelectedBankEquiv q entries i) S
  · intro i; rfl





























end CyclicSelected

end Couret.STROBO2TORS

theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries → Couret.STROBO2TORS.RecohSparseTerms),
  (∀ (i : @Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries),
      Couret.STROBO2TORS.RecohCoefficientsReduced (@Couret.STROBO2TORS.recohParitySelectedBankPrime d q inst entries i)
        (@Couret.STROBO2TORS.recohParitySelectedBankDepth d q inst entries i) (terms i)) →
    ∀ (S : Finset.{0} ((i : Fin d) → ZMod (q i))),
      Iff
        (@Eq.{1} Bool
          (@Couret.STROBO2TORS.recohCoefficientObservationCheck.{0, 0} ((i : Fin d) → ZMod (q i))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            (@Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries)
            (@instFintypeSum.{0, 0} (@Couret.STROBO2TORS.RecohEvenCoordinate d q)
              (@Couret.STROBO2TORS.RecohParitySelectedTernaryIndex d q inst entries)
              (@Subtype.fintype.{0} (Fin d)
                (fun i =>
                  @Dvd.dvd.{0} Nat Nat.instDvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q i))
                (fun a => Nat.decidable_dvd (@OfNat.ofNat.{0} Nat (nat_lit 2) (instOfNatNat (nat_lit 2))) (q a))
                (Fin.fintype d))
              (@Couret.STROBO2TORS.recohParitySelectedTernaryFintype d q inst entries))
            (@Couret.STROBO2TORS.recohSelectedSquareSupport d q entries)
            (@Couret.STROBO2TORS.recohTypedSquareValue.{0} ((i : Fin d) → ZMod (q i))
              (fun a b =>
                @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                  (Fin.fintype d) a b)
              entries)
            (@Couret.STROBO2TORS.recohParitySelectedBankPrime d q inst entries)
            (@Couret.STROBO2TORS.recohParitySelectedBankDepth d q inst entries)
            (@Couret.STROBO2TORS.recohParitySelectedBankEncoding d q inst entries) terms S)
          Bool.true)
        (@Eq.{1}
          (Prod.{0, 0} (((i : Fin d) → ZMod (q i)) → Nat)
            (@Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries → Complex))
          (@Couret.STROBO2TORS.recohObservation.{0, 0} ((i : Fin d) → ZMod (q i))
            (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
              @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            (@Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries)
            (@Couret.STROBO2TORS.recohParitySelectedObservedBank d q inst entries) S)
          (@Couret.STROBO2TORS.recohParitySelectedTypedObservation d q inst entries terms)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_parity_selected_observation_check_iff

