-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_mem_exact_decoder_iff
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:36.833098+00:00
-- url     : https://prove2.me/submissions/fc8d2fbe-e4c2-47c1-8807-40952e6023da

import Aesop
import Definitions.Def_Couret_RecohCandidateDecoder_966deca9afb6
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
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohOptimalBank_e8b60aaa0883

set_option autoImplicit false

/-!
Structured candidates for exact RECOH reconstruction.

For a genuine triple S = {a,b,c}, its three distinct off-diagonal sums
E = {a+b,a+c,b+c} belong to the support of the ordered square.  With
sigma = a+b+c, they satisfy sum E = sigma+sigma and S = sigma-E.
This supplies a complete candidate generator using only the input square.

The finite candidate generator uses decidable group operations.  The exact
complex-character filter below is explicitly noncomputable: this module
certifies its mathematical result, not an executable representation of
complex numbers or a refinement of a separate Python implementation.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]







variable [Fintype G]













theorem recoh_candidate_card_three (R : G → ℕ) (S : Finset G)
    (hS : S ∈ recohCandidates R) : S.card = 3 := by
  obtain ⟨E, sigma, _, hcard, _, rfl⟩ := (recoh_mem_candidates_iff R S).mp hS
  rw [recoh_edge_decode_card, hcard]





theorem p2m_local_recoh_mem_exact_decoder_iff {I : Type*}
    (bank : I → AddChar G ℂ) (obs : (G → ℕ) × (I → ℂ)) (S : Finset G) :
    S ∈ recohExactDecoder bank obs ↔
      S.card = 3 ∧ recohObservation bank S = obs := by
  classical
  constructor
  · intro h
    obtain ⟨hc, ho⟩ := Finset.mem_filter.mp h
    exact ⟨recoh_candidate_card_three obs.1 S hc, ho⟩
  · rintro ⟨hS, ho⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_, ho⟩
    have hsquare : orderedSquare S = obs.1 := congrArg Prod.fst ho
    rw [← hsquare]
    exact recoh_candidates_complete S hS





end Couret.STROBO2TORS


universe p2m_u_0 p2m_u_1
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] {I : Type p2m_u_1}
  (bank :
    I →
      @AddChar.{p2m_u_0, 0} G
        (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
          (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
        Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (obs : Prod.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex)) (S : Finset.{p2m_u_0} G),
  Iff
    (@Membership.mem.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} G) (Finset.{p2m_u_0} (Finset.{p2m_u_0} G))
      (@SetLike.instMembership.{p2m_u_0, p2m_u_0} (Finset.{p2m_u_0} (Finset.{p2m_u_0} G)) (Finset.{p2m_u_0} G)
        (@Finset.instSetLike.{p2m_u_0} (Finset.{p2m_u_0} G)))
      (@Couret.STROBO2TORS.recohExactDecoder.{p2m_u_0, p2m_u_1} G inst inst_1 inst_2 I bank obs) S)
    (And (@Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
      (@Eq.{max (p2m_u_0 + 1) (p2m_u_1 + 1)} (Prod.{p2m_u_0, p2m_u_1} (G → Nat) (I → Complex))
        (@Couret.STROBO2TORS.recohObservation.{p2m_u_0, p2m_u_1} G inst inst_1 I bank S) obs)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_mem_exact_decoder_iff

