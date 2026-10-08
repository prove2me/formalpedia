-- Prove2me | Theorems.Thm_GoldbachPrincipal_eventual_zero_exclusion
-- name    : GoldbachPrincipal_eventual_zero_exclusion
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-05T05:44:13.490988+00:00
-- url     : https://prove2.me/theorems/8f722e8e-4655-4f54-b33b-1a5a74b01fce
-- title:
--   Eventual exclusion of principal-character zeros in a fixed-height shrinking region
-- statement:
--   Fix a real height $H$. There exists an integer $N_0(H)>1$ such that, for every nonzero modulus $N\ge N_0(H)$ and every complex point $s\ne1$,
--   $$
--   (1-\operatorname{Re}s)\log N\le H,\qquad |\operatorname{Im}s|\le H
--   \quad\Longrightarrow\quad L(\chi_N^0,s)\ne0,
--   $$
--   where $\chi_N^0$ is the principal Dirichlet character modulo $N$.
--
--   Thus a fixed-height region with a fixed scaled real-defect cutoff eventually contains no proper zeros of the principal character. This justifies excluding that character when working in such a shrinking region. The threshold is existential: the theorem supplies no numerical value of $N_0(H)$ and no density bound for nonprincipal characters.
--
--   The statement permits any real $H$; for negative $H$ the imaginary-height condition is empty. The point $s=1$ is explicitly excluded because the principal L-function has a pole there.
--
--   **Formalization Note** The theorem is a qualitative integration corollary of existing Mathlib continuation, nonvanishing, isolated-zero, and Euler-product results. It is not a new quantitative zero-free-region estimate.
-- source:
--   Qualitative supporting corollary for the principal-character exclusion in Zhao v2, Lemma 3.1 proof, https://arxiv.org/html/2511.05631v2. Generality to arbitrary real height is an independently checked extension. Primary formal ingredients: https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/NumberTheory/LSeries/Nonvanishing.lean (riemannZeta_ne_zero_of_one_le_re); https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/NumberTheory/LSeries/DirichletContinuation.lean (LFunctionTrivChar_eq_mul_riemannZeta, differentiable_LFunctionTrivChar₁); https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/Analysis/Analytic/Order.lean (preimage_zero_mem_codiscreteWithin); https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/Topology/DiscreteSubset.lean (compact discrete sets are finite); https://github.com/leanprover-community/mathlib4/blob/777aaa61dcd2a1258d2b4962dbe983ede4d23b2e/Mathlib/Analysis/SpecialFunctions/Pow/Real.lean (norm_cpow_eq_rpow_re_of_pos, rpow_lt_one_of_one_lt_of_neg).

import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Topology.DiscreteSubset
import Mathlib.Data.Finset.Max
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

open Complex Set Filter Topology
set_option autoImplicit false

theorem GoldbachPrincipal_eventual_zero_exclusion (height : ℝ) :
    ∃ N₀ : ℕ, 1 < N₀ ∧ ∀ (N : ℕ) [NeZero N], N₀ ≤ N → ∀ z : ℂ,
      z ≠ 1 → (1-z.re)*Real.log (N:ℝ) ≤ height → |z.im| ≤ height →
      DirichletCharacter.LFunction (1 : DirichletCharacter ℂ N) z ≠ 0 := by sorry
