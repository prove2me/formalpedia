-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_representative_checked_decoder_eq_exact
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:53:09.806527+00:00
-- url     : https://prove2.me/submissions/582a150f-919d-4f11-b476-25a4e1635ea1

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_exact_decoder_iff
import Theorems.Thm_Couret_STROBO2TORS_recoh_mem_representative_checked_decoder_iff
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







/-- The representative-based algorithm has the same finite set of outputs
as the complete mathematical decoder. -/
theorem p2m_local_recoh_representative_checked_decoder_eq_exact [Fintype G]
    (reps : Finset (Finset G)) (recover : Finset G → Finset G)
    (check : Finset G → Bool) (bank : I → AddChar G ℂ)
    (obs : (G → ℕ) × (I → ℂ))
    (hcover : RecohParityCover obs.1 reps)
    (hrecover : RecohTranslationRecoverySpec bank obs recover)
    (hcheck : ∀ S, check S = true ↔ recohObservation bank S = obs) :
    recohRepresentativeCheckedDecoder reps recover check = recohExactDecoder bank obs := by
  ext S
  rw [recoh_mem_representative_checked_decoder_iff reps recover check bank obs
    hcover hrecover hcheck, recoh_mem_exact_decoder_iff]





variable [Fintype I]







section CyclicSelected

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





































































end CyclicSelected

end Couret.STROBO2TORS

universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} {I : Type p2m_u_1} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (reps : Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
  (recover : Finset.{p2m_u_0} G → Finset.{p2m_u_0} G) (check : Finset.{p2m_u_0} G → Bool)
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (obs : Prod.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex)),
  @Couret.STROBO2TORS.RecohParityCover.{p2m_u_0} G inst inst_1
      (@Prod.fst.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex) obs) reps →
    @Couret.STROBO2TORS.RecohTranslationRecoverySpec.{p2m_u_0, p2m_u_1} G inst inst_1 I bank obs recover →
      (∀ (S : Finset.{p2m_u_0} G),
          Iff (@Eq.{1} Bool (check S) Bool.true)
            (@Eq.{max (p2m_u_0 + 1) (p2m_u_1 + 1)} (Prod.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex))
              (@Couret.STROBO2TORS.recohObservation.{p2m_u_0, p2m_u_1} G inst inst_1 I bank S) obs)) →
        @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
          (@Couret.STROBO2TORS.recohRepresentativeCheckedDecoder.{p2m_u_0} G inst_1 reps recover check)
          (@Couret.STROBO2TORS.recohExactDecoder.{p2m_u_0, p2m_u_1} G inst inst_1 inst_2 I bank obs) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_representative_checked_decoder_eq_exact

