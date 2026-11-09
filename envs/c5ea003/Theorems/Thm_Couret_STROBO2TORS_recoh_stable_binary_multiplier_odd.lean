-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_stable_binary_multiplier_odd
-- name    : Couret.STROBO2TORS.recoh_stable_binary_multiplier_odd
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:29:53.266869+00:00
-- url     : https://prove2.me/theorems/05f23ab7-9f4f-416f-b548-9c8d5e9abeee
-- title:
--   Every computed binary multiplier is odd
-- statement:
--   Let $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$ with positive natural moduli $q_j$. Write $P_\chi(A)=\sum_{x\in A}\chi(x)$, $R_A$ for the ordered pair-sum count, and $F(A)$ for its fibre among triples. Let $L$ be arbitrary square entries and $j$ an even-modulus coordinate. Write $q_j=2^{k_j+1}c_j$ with $c_j$ odd. The specified multiplier $b_j(L)$ equals $2s+1$, where $s$ is the first index below $2^{k_j}$ whose fixed-precision square phase centre has squared norm at least $9/4$, or zero if none passes. Then
--
--   $$b_j(L)\text{ is odd}.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohStableSquareSelection.lean#L175-L179, lines 175–179; source file SHA-256 2f7714eca3c4e8b224d008d7909c95a42c2c459aa1c10a8588b3fe2fc9d9a1c8; theorem Couret.STROBO2TORS.recoh_stable_binary_multiplier_odd

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

theorem recoh_stable_binary_multiplier_odd
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (i : RecohEvenCoordinate q) : Odd (recohStableBinaryMultiplier q entries i) := by sorry








end Couret.STROBO2TORS
