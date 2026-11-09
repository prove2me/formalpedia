-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_square_support_card_le_six
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:42:33.441133+00:00
-- url     : https://prove2.me/submissions/07cb9c49-6f52-4745-a94f-47b150ecec90

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





/-- A genuine triple square has at most three diagonal values and three
off-diagonal values. -/
theorem p2m_local_recoh_square_support_card_le_six (S : Finset G) (hS : S.card = 3) :
    (recohSquareSupport (orderedSquare S)).card ≤ 6 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hS
  have hsub : recohSquareSupport (orderedSquare ({a, b, c} : Finset G)) ⊆
      {a + a, b + b, c + c, a + b, a + c, b + c} := by
    intro z hz
    have hp := (recoh_mem_square_support _ _).mp hz
    rw [orderedSquare_three a b c z hab hac hbc] at hp
    simpa only [Finset.mem_insert, Finset.mem_singleton] using
      square_positive_cases a b c z hp
  exact (Finset.card_le_card hsub).trans Finset.card_le_six



















end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  [inst_2 : Fintype.{p2m_u_0} G] (S : Finset.{p2m_u_0} G),
  @Eq.{1} Nat (@Finset.card.{p2m_u_0} G S) (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))) →
    @LE.le.{0} Nat instLENat
      (@Finset.card.{p2m_u_0} G
        (@Couret.STROBO2TORS.recohSquareSupport.{p2m_u_0} G inst_2
          (@Couret.STROBO2TORS.orderedSquare.{p2m_u_0} G inst inst_1 S)))
      (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_square_support_card_le_six

