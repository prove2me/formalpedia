-- Prove2me | Theorems.Thm_Couret_STROBO2TORS_recoh_stable_bank_separated_two
-- name    : Couret.STROBO2TORS.recoh_stable_bank_separated_two
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:29:54.670508+00:00
-- url     : https://prove2.me/theorems/23b555b7-2310-4a1f-abb6-a6b08564d3fd
-- title:
--   Stable-bank separation of size 2
-- statement:
--   Let $G=\prod_{j<d}\mathbb Z/q_j\mathbb Z$ with positive natural moduli. For each even coordinate $i$, let $\chi_i$ be the canonical two-primary coordinate character, of root period $N_i=2^{v_2(q_i)}$. For natural multipliers $m_i$, put $\beta_i=\chi_i^{m_i}$. Assume every $m_i$ is odd. Given square entries representing $Q_S$, let $I$ be the selected-bank index set: all even coordinates and the optional selected ternary coordinate. The stable bank $\gamma$ uses $\beta$ on binary indices and the unchanged canonical selected character on ternary indices. Write $\mathcal F(S)$ for the three-element supports with square $Q_S$, and $P_\gamma(T)=\sum_{x\in T}\gamma(x)$. Assume $|P_{\beta_i}(T)|\ge 1$ on every fibre support and binary index. Then
--
--   $$B,C\in\mathcal F(S),\ B\ne C\Longrightarrow\exists i\in I:\ |P_{\gamma_i}(B)-P_{\gamma_i}(C)|\ge 2.$$
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/eb7323762a9fa64f54f95ea7aa2981dee0ba54af/research/strobo-2tors-2026-10-12/lean/RecohStableBank.lean#L169-L182, lines 169–182; source file SHA-256 77be62a3e2bd7051471ff8ef5d23213a8670a43f693859dccdf4b62ca2c3d1e7; theorem Couret.STROBO2TORS.recoh_stable_bank_separated_two

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
import Theorems.Thm_Couret_STROBO2TORS_recoh_stable_bank_separated
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

theorem recoh_stable_bank_separated_two
    (entries : List (((i : Fin d) → ZMod (q i)) × ℕ))
    (multipliers : RecohEvenCoordinate q → ℕ) (hodd : ∀ i, Odd (multipliers i))
    (S : Finset ((i : Fin d) → ZMod (q i)))
    (hSR : orderedSquare S = recohTypedSquareValue entries)
    (hamp : ∀ T ∈ squareFibre S, ∀ i, 1 ≤ ‖recohSupportProbe
      (recohStableBinaryBank q multipliers i) T‖) :
    RecohProbeSeparated (recohStableObservedBank q entries multipliers) (squareFibre S) 2 := by sorry










end Couret.STROBO2TORS
