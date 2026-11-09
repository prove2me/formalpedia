-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_fast_candidates_complete
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:57.816195+00:00
-- url     : https://prove2.me/submissions/3b7b114c-f215-40ce-9014-aa9aa7fd2e73

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

















section FiniteRefinement

variable [Fintype G]

/-- Every valid triple is recovered from the single chosen half-sum of
its true edge set.  The difference from the true half-sum belongs to G[2]. -/
theorem p2m_local_recoh_fast_candidates_complete {I : Type*}
    (U : Finset G) (half : G → Option G) (recover : Finset G → Finset G)
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ))
    (hhalf : RecohHalfSolverSpec half)
    (hrecover : RecohTranslationRecoverySpec bank obs recover)
    (hU : recohSquareSupport obs.1 ⊆ U)
    (S : Finset G) (hS : S.card = 3) (hobs : recohObservation bank S = obs) :
    S ∈ recohFastCandidates U half recover := by
  obtain ⟨E, sigma, hE, hcard, hsigma, hdecode⟩ :=
    (recoh_mem_candidates_iff (orderedSquare S) S).mp (recoh_candidates_complete S hS)
  have hR : orderedSquare S = obs.1 := congrArg Prod.fst hobs
  rw [hR] at hE
  obtain ⟨sigma0, hsigma0⟩ := hhalf.2 (E.sum id) ⟨sigma, hsigma⟩
  have hdouble0 : sigma0 + sigma0 = E.sum id := hhalf.1 _ _ hsigma0
  have hu : (sigma - sigma0) + (sigma - sigma0) = 0 :=
    (double_eq_iff_two_torsion sigma0 sigma).mp (hdouble0.trans hsigma.symm)
  have hB : (recohEdgeDecode E sigma0).card = 3 := by
    rw [recoh_edge_decode_card, hcard]
  have hshift : translateSupport (recohEdgeDecode E sigma0) (sigma - sigma0) = S :=
    (recoh_edge_decode_change_half E sigma sigma0).symm.trans hdecode
  have hrec := hrecover.2 (recohEdgeDecode E sigma0) hB (sigma - sigma0) hu
    (by simpa only [hshift] using hobs)
  apply (recoh_mem_fast_candidates_iff U half recover S).mpr
  refine ⟨E, hE.trans hU, hcard, ?_, ?_⟩
  · simp only [hsigma0, Option.isSome_some]
  · change recover (recohEdgeDecode E ((half (E.sum id)).getD 0)) = S
    rw [hsigma0]
    exact hrec.trans hshift







end FiniteRefinement

variable {r : ℕ}

local notation "H₂" => recohTorsionSubgroup (G := G) 2











end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] {I : Type p2m_u_1} (U : Finset.{p2m_u_0} G) (half : G → Option.{p2m_u_0} G)
  (recover : Finset.{p2m_u_0} G → Finset.{p2m_u_0} G)
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
        ∀ (S : Finset.{p2m_u_0} G),
          @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
            @Eq.{max (p2m_u_0 + 1) (p2m_u_1 + 1)} (Prod.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex))
                (@Couret.STROBO2TORS.recohObservation.{p2m_u_0, p2m_u_1} G inst inst_1 I bank S) obs →
              @Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
                (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
                  (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
                (@Couret.STROBO2TORS.recohFastCandidates.{p2m_u_0} G inst inst_1 U half recover) S := @_root_.Couret.STROBO2TORS.p2m_local_recoh_fast_candidates_complete

