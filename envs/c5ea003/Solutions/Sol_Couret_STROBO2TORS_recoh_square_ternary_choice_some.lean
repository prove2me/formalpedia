-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_square_ternary_choice_some
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:57:13.263213+00:00
-- url     : https://prove2.me/submissions/66951c67-f01a-4768-ac3e-c404d8df6aaa

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



theorem recoh_first_passing_sound (test : α → Bool) (xs : List α) (a : α)
    (h : recohFirstPassing test xs = some a) : test a = true := by
  induction xs with
  | nil => simp [recohFirstPassing] at h
  | cons b xs ih =>
    by_cases hb : test b = true
    · simp only [recohFirstPassing, hb, if_true, Option.some.injEq] at h
      simpa only [← h] using hb
    · simp only [recohFirstPassing, if_neg hb] at h
      exact ih h



end FiniteSelection

section Cyclic

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]



















theorem p2m_local_recoh_square_ternary_choice_some
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (j : RecohPrimaryCoordinate q 3) (h : recohSquareTernaryChoice q entries = some j) :
    recohTernaryOrbitCheck q (recohCyclicSquareRepresentatives q entries) j = true := by
  unfold recohSquareTernaryChoice at h
  dsimp only at h
  by_cases ho : recohOneOrbitCheck (recohCyclicSquareRepresentatives q entries) = true
  · simp only [if_pos ho, reduceCtorEq] at h
  · rw [if_neg ho] at h
    exact recoh_first_passing_sound _ _ j h

















end Cyclic

end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat))
  (j : @Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))),
  @Eq.{1}
      (Option.{0}
        (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3)))))
      (@Couret.STROBO2TORS.recohSquareTernaryChoice d q inst entries)
      (@Option.some.{0}
        (@Couret.STROBO2TORS.RecohPrimaryCoordinate d q (@OfNat.ofNat.{0} Nat (nat_lit 3) (instOfNatNat (nat_lit 3))))
        j) →
    @Eq.{1} Bool
      (@Couret.STROBO2TORS.recohTernaryOrbitCheck d q inst
        (@Couret.STROBO2TORS.recohCyclicSquareRepresentatives d q entries) j)
      Bool.true := @_root_.Couret.STROBO2TORS.p2m_local_recoh_square_ternary_choice_some

