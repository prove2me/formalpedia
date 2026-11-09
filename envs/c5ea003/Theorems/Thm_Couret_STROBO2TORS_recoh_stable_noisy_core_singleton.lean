-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_stable_noisy_core_singleton
-- name    : Couret.STROBO2TORS.recoh_stable_noisy_core_singleton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:44:21.533359+00:00
-- url     : https://prove2.me/theorems/3bf2fa00-5370-418b-b478-9335d6c04b28
-- title:
--   The stable noisy core exactly recovers a triple
-- statement:
--   Let $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$ with positive natural moduli $q_j$. Write $P_\chi(A)=\sum_{x\in A}\chi(x)$, $R_A$ for the ordered pair-sum count, and $F(A)$ for its fibre among triples. For square entries $L$, let $\mathcal B_L$ be the computed stable bank, using the specified square-only odd-power binary multiplier selection and square-selected ternary coordinate, and let $I_L$ be its selected index type. Let $A_m(x)=\sum_{j<m}(-1)^j x^{2j+1}/(2j+1)$, $p_m=16A_m(1/5)-4A_m(1/239)$ and $e_m=16(1/5)((1/5)^2)^m/(1-(1/5)^2)+4(1/239)((1/239)^2)^m/(1-(1/239)^2)$. Put $E_{m,n}=2e_m+2\cdot8^n/n!$. Rational-complex centres are interpreted as complex numbers. For rational $0\le\epsilon<1$, put $\eta=(1-\epsilon)/4$, $\tau=\epsilon+\eta$. Call $(m,n)$ valid when $|p_m|\le4$, $n\ge15$ and $3E_{m,n}\le\eta$. The stable noisy core generates one recovered candidate per cyclic square representative using binary signs, then filters by rational balls of radius $\tau$ around all predicted stable-bank readings. The guarded decoder first checks the typed square format and valid precision, returning the empty set if either fails. Let $A$ be a triple with $R_A=R_L$, and let rational-complex observations $o_i$ satisfy $|o_i-P_{\mathcal B_L(i)}(A)|\le\epsilon$ for every $i$. Suppose $(m,n)$ is valid. Then
--
--   $$\operatorname{Core}(L,o,\epsilon,m,n)=\{A\}.$$
--
--   The exact square remains part of the observation contract.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohStableReconstruction.lean#L201-L233, lines 201–233; source file SHA-256 6ba847ab84346711528fad14d2971d71a5bd99f9152b733aa4ad067c05fd8df3; theorem Couret.STROBO2TORS.recoh_stable_noisy_core_singleton

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_cyclic_square_representatives_complete
import Theorems.Thm_Couret_STROBO2TORS_recoh_noisy_sign_decoder_singleton
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_bank_separated_two
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_binary_amplitude
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_binary_bank_sign_coordinates
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_binary_multiplier_odd
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_predicted_reading_error
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

theorem recoh_stable_noisy_core_singleton
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (S : Finset ((i : Fin d) → ZMod (q i))) (hS : S.card = 3)
    (hR : orderedSquare S = recohTypedSquareValue entries)
    (observed : RecohSelectedBankIndex q entries → RecohRationalComplex)
    (epsilon : ℚ) (machinTerms taylorTerms : ℕ)
    (hprecision : RecohStablePrecisionValid epsilon machinTerms taylorTerms)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) -
      recohSupportProbe (recohComputedStableBank q entries i) S‖ ≤ (epsilon : ℝ)) :
    recohStableNoisyCore q entries observed epsilon machinTerms taylorTerms = {S} := by sorry












end Couret.STROBO2TORS
