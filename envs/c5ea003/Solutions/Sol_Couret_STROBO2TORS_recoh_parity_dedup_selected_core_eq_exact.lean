-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_parity_dedup_selected_core_eq_exact
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:21.986189+00:00
-- url     : https://prove2.me/submissions/ac06dfa9-80e7-4cf2-8294-f8a9391a788b

import Aesop
import Definitions.Def_Couret_RecohParityDedupTransport_fd9d6ec554ae
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_dedup_cover
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_observation_check_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_recovery_spec
import Theorems.Thm_Couret_STROBO2TORS_recoh_representative_checked_decoder_eq_exact
import Definitions.Def_Couret_RecohParityDecoder_e5701300ff06

set_option autoImplicit false

/-!
Transport through the explicit anchored deduplication model.

An enumeration and an anchor remain explicit inputs with representation
contracts. The decoder really recovers from the retained representatives.
The fibre classification bounds their number by two, without assuming that
the supplied square data are realizable. No Python list-order or JSON
equivalence is claimed by this module.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G I : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]











section CyclicSelected

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]









theorem p2m_local_recoh_parity_dedup_selected_core_eq_exact
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (xs : List (Finset ((i : Fin d) → ZMod (q i))))
    (hxs : xs.toFinset = recohCyclicParityRepresentatives q entries)
    (anchor : Finset ((i : Fin d) → ZMod (q i)) → ((i : Fin d) → ZMod (q i)))
    (hanchor : ∀ B ∈ xs, anchor B ∈ B)
    (hred : ∀ i, RecohCoefficientsReduced
      (recohParitySelectedBankPrime q entries i)
      (recohParitySelectedBankDepth q entries i) (terms i)) :
    recohParityDedupSelectedCore q entries terms xs anchor =
      recohExactDecoder (recohParitySelectedObservedBank q entries)
        (recohParitySelectedTypedObservation q entries terms) := by
  apply recoh_representative_checked_decoder_eq_exact
    (recohAnchoredOrbitDedup anchor xs).toFinset
    (recohIndexedRecoverSupport (recohProductTwoCoordinates q)
      (recohCoefficientSignBools Sum.inl (recohParitySelectedBankPrime q entries)
        (recohParitySelectedBankDepth q entries)
        (recohParitySelectedBankEncoding q entries) terms))
    (recohCoefficientObservationCheck (recohSelectedSquareSupport q entries)
      (recohTypedSquareValue entries) (recohParitySelectedBankPrime q entries)
      (recohParitySelectedBankDepth q entries)
      (recohParitySelectedBankEncoding q entries) terms)
    (recohParitySelectedObservedBank q entries)
    (recohParitySelectedTypedObservation q entries terms)
  · exact recoh_parity_dedup_cover
      (recohSelectedSquareSupport q entries) (recohTypedSquareValue entries)
      (recohProductHalf q) (recoh_product_half_spec q)
      (recoh_selected_square_support_covered q entries) xs hxs anchor hanchor
  · exact recoh_parity_selected_recovery_spec q entries terms hred
  · exact recoh_parity_selected_observation_check_iff q entries terms hred











end CyclicSelected

end Couret.STROBO2TORS

theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries → Couret.STROBO2TORS.RecohSparseTerms)
  (xs : List.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))),
  @Eq.{1} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
      (@List.toFinset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
        (fun a b =>
          @Finset.decidableEq.{0} ((i : Fin d) → ZMod (q i))
            (fun a b =>
              @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                (Fin.fintype d) a b)
            a b)
        xs)
      (@Couret.STROBO2TORS.recohCyclicParityRepresentatives d q entries) →
    ∀ (anchor : Finset.{0} ((i : Fin d) → ZMod (q i)) → (i : Fin d) → ZMod (q i)),
      (∀ (B : Finset.{0} ((i : Fin d) → ZMod (q i))),
          @Membership.mem.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i)))
              (List.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
              (@List.instMembership.{0} (Finset.{0} ((i : Fin d) → ZMod (q i)))) xs B →
            @Membership.mem.{0, 0} ((i : Fin d) → ZMod (q i)) (Finset.{0} ((i : Fin d) → ZMod (q i)))
              (@SetLike.instMembership.{0, 0} (Finset.{0} ((i : Fin d) → ZMod (q i))) ((i : Fin d) → ZMod (q i))
                (@Finset.instSetLike.{0} ((i : Fin d) → ZMod (q i))))
              B (anchor B)) →
        (∀ (i : @Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries),
            Couret.STROBO2TORS.RecohCoefficientsReduced
              (@Couret.STROBO2TORS.recohParitySelectedBankPrime d q inst entries i)
              (@Couret.STROBO2TORS.recohParitySelectedBankDepth d q inst entries i) (terms i)) →
          @Eq.{1} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
            (@Couret.STROBO2TORS.recohParityDedupSelectedCore d q inst entries terms xs anchor)
            (@Couret.STROBO2TORS.recohExactDecoder.{0, 0} ((i : Fin d) → ZMod (q i))
              (@Pi.addCommGroup.{0, 0} (Fin d) (fun i => ZMod (q i)) fun i =>
                @Ring.toAddCommGroup.{0} (ZMod (q i)) (@CommRing.toRing.{0} (ZMod (q i)) (ZMod.commRing (q i))))
              (fun a b =>
                @Fintype.decidablePiFintype.{0, 0} (Fin d) (fun a => ZMod (q a)) (fun a => ZMod.decidableEq (q a))
                  (Fin.fintype d) a b)
              (@Pi.instFintype.{0, 0} (Fin d) (fun i => ZMod (q i)) (instDecidableEqFin d) (Fin.fintype d) fun a =>
                @ZMod.fintype (q a) (inst a))
              (@Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries)
              (@Couret.STROBO2TORS.recohParitySelectedObservedBank d q inst entries)
              (@Couret.STROBO2TORS.recohParitySelectedTypedObservation d q inst entries terms)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_parity_dedup_selected_core_eq_exact

