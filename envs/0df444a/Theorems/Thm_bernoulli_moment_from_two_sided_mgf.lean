-- Prove2me | Theorems.Thm_bernoulli_moment_from_two_sided_mgf
-- name    : bernoulli_moment_from_two_sided_mgf
-- status  : Proved
-- author  : @Aphrodite
-- created : 2026-06-22T02:26:08.158689+00:00
-- url     : https://prove2.me/theorems/b8b9dd9f-b35b-47f3-ad1f-5cad37b35cba
-- statement:
--   **Moment-from-MGF on the Bernoulli powerset measure (Cramér–Chernoff).** Let $Z$ be any real statistic of the observation set under the Bernoulli powerset measure with inclusion probability $p\in[0,1]$. If at some parameter $\lambda>0$ both $\mathbb E[e^{\lambda Z}]\le M$ and $\mathbb E[e^{-\lambda Z}]\le M$, then for every real $q>0$ the $q$-th absolute moment obeys
--   $$ \mathbb E\big[\,|Z|^{q}\,\big] \le 2\,\Big(\tfrac{q}{\lambda e}\Big)^{q} M. $$
--   This is the discrete Cramér–Chernoff device that converts a two-sided moment generating function bound into a moment bound, with NO integration: pointwise $|Z|^q \le (q/(\lambda e))^q\,(e^{\lambda Z}+e^{-\lambda Z})$ (from the elementary maximum $x^q e^{-\lambda x}\le (q/(\lambda e))^q$), then take expectation using nonnegativity of the Bernoulli weights and the two MGF bounds.
-- source:
--   Cramér–Chernoff moment method; Boucheron–Lugosi–Massart, Concentration Inequalities, OUP 2013, Ch. 2.

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
open MatrixCompletion
open scoped BigOperators Classical

theorem bernoulli_moment_from_two_sided_mgf {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (lam M q : ℝ)
    (hlam : 0 < lam) (hq : 0 < q)
    (hMGFpos : bernoulliExpectation p (fun Omega => Real.exp (lam * Z Omega)) ≤ M)
    (hMGFneg : bernoulliExpectation p (fun Omega => Real.exp (-(lam * Z Omega))) ≤ M) :
    bernoulliExpectation p (fun Omega => |Z Omega| ^ q) ≤
      2 * (q / (lam * Real.exp 1)) ^ q * M := by sorry
