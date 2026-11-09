-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_parity_representatives_card_le_six
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:43:01.298529+00:00
-- url     : https://prove2.me/submissions/4a287244-50f5-4b05-8995-0b28ebeba1c9

import Aesop
import Definitions.Def_Couret_RecohParityGenerator_deb90a4bb68d
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a

set_option autoImplicit false
set_option maxRecDepth 2000

/-!
The compact parity generator for three-point ordered squares.

All executable searches are over the supplied finite square support U,
one residual set, or its two-element subsets. There is no `Fintype G`
assumption on the generator. The final exact-square test is performed after
the chosen translation; the translation identity below relates it to the
normalized square test used by Python v0.2.

This module proves a mathematical coverage contract for these Lean
definitions. It does not provide a semantics for Python, JSON or its runtime.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {G : Type*} [AddCommGroup G] [DecidableEq G]



































































theorem recoh_parity_single_seeds_card_le_six
    (U : Finset G) (R : G → ℕ) (half : G → Option G) (d : G) :
    (recohParitySingleSeeds U R half d).card ≤ 6 := by
  unfold recohParitySingleSeeds
  split_ifs with h
  · cases half d with
    | none => simp
    | some c =>
      apply Finset.card_image_le.trans
      apply (Finset.card_filter_le _ _).trans
      rw [Finset.card_powersetCard, h.1]
      decide
  · simp

theorem recoh_parity_raw_seeds_card_le_six
    (U : Finset G) (R : G → ℕ) (half : G → Option G) :
    (recohParityRawSeeds U R half).card ≤ 6 := by
  unfold recohParityRawSeeds
  split_ifs with h3 hg h1
  · cases half ((recohParityEdges U R).sum id) <;> simp
  · simp
  · obtain ⟨d, hd⟩ := Finset.card_eq_one.mp h1
    rw [hd]
    simpa using recoh_parity_single_seeds_card_le_six U R half d
  · simp

/-- At most six raw local choices can reach the final square filter. -/
theorem p2m_local_recoh_parity_representatives_card_le_six
    (U : Finset G) (R : G → ℕ) (half : G → Option G) :
    (recohParityRepresentatives U R half).card ≤ 6 :=
  (Finset.card_filter_le _ _).trans (recoh_parity_raw_seeds_card_le_six U R half)

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G] (U : Finset.{p2m_u_0} G)
  (R : G → Nat) (half : G → Option.{p2m_u_0} G),
  @LE.le.{0} Nat instLENat
    (@Finset.card.{p2m_u_0} (Finset.{p2m_u_0} G)
      (@Couret.STROBO2TORS.recohParityRepresentatives.{p2m_u_0} G inst inst_1 U R half))
    (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_parity_representatives_card_le_six

