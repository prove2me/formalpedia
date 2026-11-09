-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_stable_binary_multiplier_odd
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:29:56.462204+00:00
-- url     : https://prove2.me/submissions/34cf1501-0391-45f3-9964-60165316fb85

import Aesop
import Definitions.Def_Couret_RecohStableSquareSelection_4ccedec76589
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Rat.Cast.Order
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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_RecohRationalRoots_2e1442988636
import Definitions.Def_Couret_RecohOddPowerRuntime_8c8d44664d18
import Definitions.Def_Couret_RecohSquareSelector_3b7a2954c02a
import Definitions.Def_Couret_RecohReconstruction_b9109c17baa8

set_option autoImplicit false

/-!
The robust binary multipliers are computed from the exact labelled square.
Rational phase centres have a proved error budget.  The finite odd-power
search compares their squared norms to 9/4 and falls back to exponent one.
No support or measured character value is an input to this computation.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators









variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

















theorem p2m_local_recoh_stable_binary_multiplier_odd
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (i : RecohEvenCoordinate q) : Odd (recohStableBinaryMultiplier q entries i) := by
  exact ⟨recohOddSquaredChoice (2 ^ (recohCanonicalPrimaryData q 2).exponent i)
    (recohStableBinarySquareNorm q entries i), rfl⟩







end Couret.STROBO2TORS


theorem solution : ∀ {d : Nat} (q : Fin d → Nat)
  [inst : ∀ (i : Fin d), @NeZero.{0} Nat (@MulZeroClass.toZero.{0} Nat Nat.instMulZeroClass) (q i)]
  (entries : List.{0} (Prod.{0, 0} ((i : Fin d) → ZMod (q i)) Nat)) (i : @Couret.STROBO2TORS.RecohEvenCoordinate d q),
  @Odd.{0} Nat Nat.instSemiring (@Couret.STROBO2TORS.recohStableBinaryMultiplier d q inst entries i) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_stable_binary_multiplier_odd

