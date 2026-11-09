-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_first_passing_exists
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:53:21.528177+00:00
-- url     : https://prove2.me/submissions/af8f30bb-4fe1-4714-9a8a-013bc293e693

import Aesop
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a
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
import Definitions.Def_Couret_RecohCyclicPreparedDecoder_0ae8cdf0a932
import Definitions.Def_Couret_RecohTernaryFibreSelector_4c0db0f29983

set_option autoImplicit false

/-!
Selection from the labelled ordered square using at most twenty explicit
representatives. All runtime checks use finite supports, cyclic coordinates
and integer cyclotomic coefficients. No ambient-group search occurs.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G] [DecidableEq G]























variable [Fintype G]



section FiniteSelection

variable {α : Type*}





theorem p2m_local_recoh_first_passing_exists (test : α → Bool) (xs : List α)
    (h : ∃ a ∈ xs, test a = true) : ∃ a, recohFirstPassing test xs = some a := by
  induction xs with
  | nil => simp at h
  | cons b xs ih =>
    by_cases hb : test b = true
    · exact ⟨b, by simp only [recohFirstPassing, hb, if_true]⟩
    · have hex : ∃ a ∈ xs, test a = true := by
        obtain ⟨a, ha, ht⟩ := h
        rcases List.mem_cons.mp ha with rfl | ha
        · exact (hb ht).elim
        · exact ⟨a, ha, ht⟩
      obtain ⟨a, ha⟩ := ih hex
      exact ⟨a, by simp only [recohFirstPassing, if_neg hb, ha]⟩

end FiniteSelection

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]





































end Cyclic

end Couret.STROBO2TORS


universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} (test : α → Bool) (xs : List.{p2m_u_0} α),
  (@Exists.{p2m_u_0 + 1} α fun a =>
      And (@Membership.mem.{p2m_u_0, p2m_u_0} α (List.{p2m_u_0} α) (@List.instMembership.{p2m_u_0} α) xs a)
        (@Eq.{1} Bool (test a) Bool.true)) →
    @Exists.{p2m_u_0 + 1} α fun a =>
      @Eq.{p2m_u_0 + 1} (Option.{p2m_u_0} α) (@Couret.STROBO2TORS.recohFirstPassing.{p2m_u_0} α test xs)
        (@Option.some.{p2m_u_0} α a) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_first_passing_exists

