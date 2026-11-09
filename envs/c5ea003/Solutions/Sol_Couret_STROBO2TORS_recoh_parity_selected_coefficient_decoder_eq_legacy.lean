-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_parity_selected_coefficient_decoder_eq_legacy
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:29:37.311227+00:00
-- url     : https://prove2.me/submissions/5d1bc710-4a3f-485c-a853-6d61e211405c

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_parity_selected_coefficient_decoder_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_selected_coefficient_decoder_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_input_format_iff_legacy
import Theorems.Thm_Couret_STROBO2TORS_recoh_parity_selected_observation_iff_legacy
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































































/-- Equality for every already typed input, with the same guards and the
same measured slots under the explicit index equivalence. -/
theorem p2m_local_recoh_parity_selected_coefficient_decoder_eq_legacy
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (terms : RecohParitySelectedBankIndex q entries → RecohSparseTerms) :
    recohParitySelectedCoefficientDecoder q entries terms =
      recohSelectedCoefficientDecoder q entries (recohParitySelectedLegacyTerms q entries terms) := by
  ext S
  rw [recoh_mem_parity_selected_coefficient_decoder_iff,
    recoh_mem_selected_coefficient_decoder_iff,
    recoh_parity_selected_input_format_iff_legacy,
    recoh_parity_selected_observation_iff_legacy]





end CyclicSelected

end Couret.STROBO2TORS

theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (terms : @Couret.STROBO2TORS.RecohParitySelectedBankIndex d q inst entries → Couret.STROBO2TORS.RecohSparseTerms),
  @Eq.{1} (Finset.{0} (Finset.{0} ((i : Fin d) → ZMod (q i))))
    (@Couret.STROBO2TORS.recohParitySelectedCoefficientDecoder d q inst entries terms)
    (@Couret.STROBO2TORS.recohSelectedCoefficientDecoder d q inst entries
      (@Couret.STROBO2TORS.recohParitySelectedLegacyTerms d q inst entries terms)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_parity_selected_coefficient_decoder_eq_legacy

