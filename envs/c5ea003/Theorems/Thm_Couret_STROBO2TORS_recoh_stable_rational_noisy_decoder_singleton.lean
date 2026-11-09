-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_stable_rational_noisy_decoder_singleton
-- name    : Couret.STROBO2TORS.recoh_stable_rational_noisy_decoder_singleton
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:57:37.24471+00:00
-- url     : https://prove2.me/theorems/9e9f69b5-3316-4df7-8ebf-cddc543fbe9e
-- title:
--   The rational stable noisy decoder returns the true singleton
-- statement:
--   Let $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$ with positive natural moduli. For each even coordinate $i$, let $\chi_i$ be the canonical two-primary coordinate character, of root period $N_i=2^{v_2(q_i)}$. For natural multipliers $m_i$, put $\beta_i=\chi_i^{m_i}$. Assume every $m_i$ is odd. Given square entries representing $Q_S$, let $I$ be the selected-bank index set: all even coordinates and the optional selected ternary coordinate. The stable bank $\gamma$ uses $\beta$ on binary indices and the unchanged canonical selected character on ternary indices. Write $\mathcal F(S)$ for the three-element supports with square $Q_S$, and $P_\gamma(T)=\sum_{x\in T}\gamma(x)$. Assume $|P_{\beta_i}(T)|\ge1$ for every $T\in\mathcal F(S)$ and even coordinate $i$. Let $C\subseteq\mathcal F(S)$ be a finite candidate family, let $\widehat p_i(T),o_i$ be complex numbers with rational real and imaginary parts, and let $\rho\in\mathbb Q$. The rational noisy decoder keeps $T\in C$ if $\rho\ge0$ and $|o_i-\widehat p_i(T)|^2\le\rho^2$ for every $i$. Assume $\rho\ge0$, $B\in C$, uniform prediction error at most $\eta$, observation error $|o_i-P_{\gamma_i}(B)|\le\varepsilon$, and
--
--   $$\varepsilon+\eta\le\rho,\qquad\rho+\eta<1.$$
--
--   Then the noisy decoder equals $\{B\}$.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohStableBank.lean#L251-L278, lines 251–278; source file SHA-256 77be62a3e2bd7051471ff8ef5d23213a8670a43f693859dccdf4b62ca2c3d1e7; theorem Couret.STROBO2TORS.recoh_stable_rational_noisy_decoder_singleton

import Aesop
import Definitions.Def_Couret_RecohStableBank_b01db9b053a3
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.AddChar
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Multiset.Sort
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Log
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
import Theorems.Thm_Couret_STROBO2TORS_recoh_rational_noisy_decoder_singleton
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_bank_separated_two
import Definitions.Def_Couret_RecohSelectedDecoder_a1594570d3fe
import Definitions.Def_Couret_RecohProbeStability_e389a2280f15
import Definitions.Def_Couret_RecohNoisyUniqueness_7e21ca0c53e8

set_option autoImplicit false

/-!
Quantitative reconstruction with the square-selected minimum-size bank.
Each binary character is replaced by a prescribed odd power; the selected
ternary character and the measurement index type are unchanged.

The multipliers are parameters of the bank and are fixed before readings are
received. The quantitative theorems require a certified amplitude bound on
the square fibre. A separate square-only selector supplies these parameters
and that bound.

The rational-decoder bridges use a supplied candidate set contained in the
fibre. They do not introduce an executable enumeration of the ambient group
or its powerset. Prediction error is included in the uniqueness budget.
-/

namespace Couret.STROBO2TORS



variable {d : ℕ} (q : Fin d → ℕ) [∀ i, NeZero (q i)]

theorem recoh_stable_rational_noisy_decoder_singleton
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (multipliers : RecohEvenCoordinate q → ℕ) (hodd : ∀ i, Odd (multipliers i))
    (S : Finset ((i : Fin d) → ZMod (q i)))
    (hSR : orderedSquare S = recohTypedSquareValue entries)
    (hamp : ∀ T ∈ squareFibre S, ∀ i, 1 ≤ ‖recohSupportProbe
      (recohStableBinaryBank q multipliers i) T‖)
    (candidates : Finset (Finset ((i : Fin d) → ZMod (q i))))
    (hsub : candidates ⊆ squareFibre S)
    (predicted : Finset ((i : Fin d) → ZMod (q i)) →
      RecohSelectedBankIndex q entries → RecohRationalComplex)
    (observed : RecohSelectedBankIndex q entries → RecohRationalComplex)
    (radius : ℚ) (ε η : ℝ) (hradius : 0 ≤ radius)
    (B : Finset ((i : Fin d) → ZMod (q i))) (hB : B ∈ candidates)
    (hpred : ∀ T ∈ candidates, ∀ i, ‖recohRationalComplexValue (predicted T i) -
      recohSupportProbe (recohStableObservedBank q entries multipliers i) T‖ ≤ η)
    (hobs : ∀ i, ‖recohRationalComplexValue (observed i) -
      recohSupportProbe (recohStableObservedBank q entries multipliers i) B‖ ≤ ε)
    (hcomplete : ε + η ≤ (radius : ℝ)) (hunique : (radius : ℝ) + η < 1) :
    recohRationalNoisyDecoder candidates predicted observed radius = {B} := by sorry


end Couret.STROBO2TORS
