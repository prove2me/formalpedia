-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_parity_selected_coefficient_core_eq_exact
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:07:50.889627+00:00
-- url     : https://prove2.me/submissions/27efa57d-d252-45ae-acd6-a62f167ffe2f

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_binary_bank_sign_coordinates
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_binary_probe_nonzero
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_coefficient_backend_eq_exact
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









































/-- All parity, half-solver, coordinate, encoder and root contracts are
proved from q. The only remaining coefficient condition is exponent range. -/
theorem p2m_local_recoh_parity_selected_coefficient_core_eq_exact
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms)
    (hred : ∀ i, RecohCoefficientsReduced
      (recohParitySelectedBankPrime q entries i)
      (recohParitySelectedBankDepth q entries i) (terms i)) :
    recohParitySelectedCoefficientCore q entries terms =
      recohExactDecoder (recohParitySelectedObservedBank q entries)
        (recohParitySelectedTypedObservation q entries terms) := by
  apply recoh_parity_coefficient_backend_eq_exact
    (recohSelectedSquareSupport q entries) (recohTypedSquareValue entries)
    (recohProductHalf q) Sum.inl (recohProductTwoCoordinates q)
    (recohParitySelectedBankPrime q entries) (recohParitySelectedBankDepth q entries)
    (recohParitySelectedBankEncoding q entries) terms
    (recohParitySelectedObservedBank q entries) (recohParitySelectedBankRoot q entries)
    (fun i => recohCoefficientValue (recohParitySelectedBankRoot q entries i) (terms i))
  · exact recoh_product_half_spec q
  · exact recoh_selected_square_support_covered q entries
  · intro i
    exact recoh_selected_bank_prime q entries (recohParitySelectedBankEquiv q entries i)
  · intro i
    exact recoh_selected_bank_root_primitive q entries (recohParitySelectedBankEquiv q entries i)
  · exact hred
  · intro i S
    exact recoh_selected_bank_encoding_interpret q entries
      (recohParitySelectedBankEquiv q entries i) S
  · intro i; rfl
  · intro u i
    exact recoh_cyclic_binary_bank_sign_coordinates q (recohCanonicalPrimaryData q 2) u i
  · intro i S hS
    exact recoh_cyclic_binary_probe_nonzero q (recohCanonicalPrimaryData q 2) i S hS



























end CyclicSelected

end Couret.STROBO2TORS

theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries → Couret.STROBO2TORS.RecohSparseTerms),
  (∀ (i : @Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries),
      Couret.STROBO2TORS.RecohCoefficientsReduced (@Couret.STROBO2TORS.recohParitySelectedBankPrime d q inst entries i)
        (@Couret.STROBO2TORS.recohParitySelectedBankDepth d q inst entries i) (terms i)) →
    @Eq.{1} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
      (@Couret.STROBO2TORS.recohParitySelectedCoefficientCore d q inst entries terms)
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
        (@Couret.STROBO2TORS.recohParitySelectedTypedObservation d q inst entries terms)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_parity_selected_coefficient_core_eq_exact

