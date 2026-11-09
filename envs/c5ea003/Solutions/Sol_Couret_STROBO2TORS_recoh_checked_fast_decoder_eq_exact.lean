-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_checked_fast_decoder_eq_exact
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:46:26.425801+00:00
-- url     : https://prove2.me/submissions/261b5203-6670-41bb-bd3d-0fd81ebab4c6

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













/-- A correct Boolean checker gives exactly the mathematical complex filter. -/
theorem recoh_checked_fast_decoder_eq_fast {I : Type*}
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (check : Finset G → Bool) (bank : I → AddChar G ℂ)
    (obs : (G → ℕ) × (I → ℂ))
    (hcheck : ∀ S : Finset G, check S = true ↔ recohObservation bank S = obs) :
    recohCheckedFastDecoder U half recover check =
      recohFastDecoder U half recover bank obs := by
  classical
  ext S
  simp only [recohCheckedFastDecoder, recohFastDecoder, Finset.mem_filter, hcheck]

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

/-- A verified exact-arithmetic Boolean backend preserves the full
refinement theorem without changing the candidate construction. -/
theorem p2m_local_recoh_checked_fast_decoder_eq_exact {I : Type*}
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (check : Finset G → Bool) (bank : I → AddChar G ℂ)
    (obs : (G → ℕ) × (I → ℂ))
    (hhalf : RecohHalfSolverSpec half)
    (hrecover : RecohTranslationRecoverySpec bank obs recover)
    (hU : recohSquareSupport obs.1 ⊆ U)
    (hcheck : ∀ S : Finset G, check S = true ↔ recohObservation bank S = obs) :
    recohCheckedFastDecoder U half recover check = recohExactDecoder bank obs := by
  rw [recoh_checked_fast_decoder_eq_fast U half recover check bank obs hcheck]
  exact recoh_fast_decoder_eq_exact U half recover bank obs hhalf hrecover hU

end FiniteRefinement

variable {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2











end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] {I : Type p2m_u_1} (U : Finset.{p2m_u_0} G) (half : G → Option.{p2m_u_0} G)
  (recover : Finset.{p2m_u_0} G → Finset.{p2m_u_0} G) (check : Finset.{p2m_u_0} G → Bool)
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (obs : Prod.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex)),
  @Couret.STROBO2TORS.RecohHalfSolverSpec.{p2m_u_0} G inst half →
    @Couret.STROBO2TORS.RecohTranslationRecoverySpec.{p2m_u_0, p2m_u_1} G inst inst_1 I bank obs recover →
      @HasSubset.Subset.{p2m_u_0} (Finset.{p2m_u_0} G) (@Finset.instHasSubset.{p2m_u_0} G)
          (@Couret.STROBO2TORS.recohSquareSupport.{p2m_u_0} G inst_2
            (@Prod.fst.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex) obs))
          U →
        (∀ (S : Finset.{p2m_u_0} G),
            Iff (@Eq.{1} Bool (check S) Bool.true)
              (@Eq.{max (p2m_u_0 + 1) (p2m_u_1 + 1)} (Prod.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex))
                (@Couret.STROBO2TORS.recohObservation.{p2m_u_0, p2m_u_1} G inst inst_1 I bank S) obs)) →
          @Eq.{p2m_u_0 + 1} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
            (@Couret.STROBO2TORS.recohCheckedFastDecoder.{p2m_u_0} G inst inst_1 U half recover check)
            (@Couret.STROBO2TORS.recohExactDecoder.{p2m_u_0, p2m_u_1} G inst inst_1 inst_2 I bank obs) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_checked_fast_decoder_eq_exact

