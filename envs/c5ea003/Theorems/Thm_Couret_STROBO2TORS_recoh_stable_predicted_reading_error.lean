-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_stable_predicted_reading_error
-- name    : Couret.STROBO2TORS.recoh_stable_predicted_reading_error
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:31:05.586634+00:00
-- url     : https://prove2.me/theorems/98cd9e34-db17-4175-8b67-68ec82b9cf74
-- title:
--   Every computed predicted slot has its certified tolerance
-- statement:
--   Let $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$ with positive natural moduli $q_j$. Write $P_\chi(A)=\sum_{x\in A}\chi(x)$, $R_A$ for the ordered pair-sum count, and $F(A)$ for its fibre among triples. For square entries $L$, let $\mathcal B_L$ be the computed stable bank, using the specified square-only odd-power binary multiplier selection and square-selected ternary coordinate, and let $I_L$ be its selected index type. Let $A_m(x)=\sum_{j<m}(-1)^j x^{2j+1}/(2j+1)$, $p_m=16A_m(1/5)-4A_m(1/239)$ and $e_m=16(1/5)((1/5)^2)^m/(1-(1/5)^2)+4(1/239)((1/239)^2)^m/(1-(1/239)^2)$. Put $E_{m,n}=2e_m+2\cdot8^n/n!$. Rational-complex centres are interpreted as complex numbers. For rational $0\le\epsilon<1$, put $\eta=(1-\epsilon)/4$, $\tau=\epsilon+\eta$. Call $(m,n)$ valid when $|p_m|\le4$, $n\ge15$ and $3E_{m,n}\le\eta$. For valid $(m,n)$, every triple $A$ and every selected slot $i\in I_L$, the specified rational predicted reading $v_{m,n}(A,i)$ satisfies
--
--   $$|v_{m,n}(A,i)-P_{\mathcal B_L(i)}(A)|\le\eta.$$
--
--   The triple need not realize $R_L$ for this prediction bound.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohStableReconstruction.lean#L145-L170, lines 145–170; source file SHA-256 6ba847ab84346711528fad14d2971d71a5bd99f9152b733aa4ad067c05fd8df3; theorem Couret.STROBO2TORS.recoh_stable_predicted_reading_error

import Aesop
import Definitions.Def_Couret_RecohStableReconstruction_da64f089b51e
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
import Mathlib.Data.Nat.Log
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
import Mathlib.Topology.Algebra.Order.Floor
import Theorems.Thm_Couret_STROBO2TORS_recoh_support_phase_center_error
import Definitions.Def_Couret_RecohStableSquareSelection_4ccedec76589
import Definitions.Def_Couret_RecohStableBank_b01db9b053a3
import Definitions.Def_Couret_RecohNoisySignRecovery_25d41afc9bfe
import Definitions.Def_Couret_RecohRationalRoots_2e1442988636

set_option autoImplicit false

/-!
End-to-end stable reconstruction on explicit cyclic products.  The square
determines the bank, rational series determine the prediction centres, and
the decoder generates at most one candidate per square representative.
Precision is supplied by two natural numbers and checked by rational guards.
No complex comparison occurs in the executable definitions.
-/

namespace Couret.STROBO2TORS

open scoped BigOperators

variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_stable_predicted_reading_error
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (epsilon : ℚ) (machinTerms taylorTerms : ℕ)
    (hprecision : RecohStablePrecisionValid epsilon machinTerms taylorTerms)
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (i : RecohSelectedBankIndex q entries) :
    ‖recohRationalComplexValue (recohStablePredictedReading q entries machinTerms taylorTerms S i) -
      recohSupportProbe (recohComputedStableBank q entries i) S‖ ≤
        (recohStablePredictionTolerance epsilon : ℝ) := by sorry




















end Couret.STROBO2TORS
