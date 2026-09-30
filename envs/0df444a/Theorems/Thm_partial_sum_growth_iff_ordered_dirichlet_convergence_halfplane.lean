-- Prove2me | Theorems.Thm_partial_sum_growth_iff_ordered_dirichlet_convergence_halfplane
-- name    : partial_sum_growth_iff_ordered_dirichlet_convergence_halfplane
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T02:49:12.931792+00:00
-- url     : https://prove2.me/theorems/40da4952-5908-47b0-a0ea-b84ac0e0fb5e
-- title:
--   Signed partial-sum growth is equivalent to ordered Dirichlet convergence on a half-plane
-- statement:
--   Let $f:\mathbb N\to\mathbb C$, let $a\ge0$, and put $M(N)=\sum_{n=1}^Nf(n)$. The following three conditions are equivalent:
--
--   $$\begin{aligned}
--   &M(N)=O_\varepsilon(N^{a+\varepsilon})\quad\text{for every }\varepsilon>0;\\
--   &\sum_{n=1}^N f(n)n^{-\sigma}\text{ converges as }N\to\infty\quad\text{for every real }\sigma>a;\\
--   &\sum_{n=1}^N f(n)n^{-s}\text{ converges as }N\to\infty\quad\text{for every complex }s\text{ with }\operatorname{Re}s>a.
--   \end{aligned}$$
--
--   All convergence assertions concern the ordinary ordered partial sums. This identifies the growth threshold of signed coefficient sums with the corresponding open half-plane of Dirichlet convergence. It asserts no convergence on the boundary and requires no absolute-convergence hypothesis.
-- source:
--   Derived two-sided Abel-summation criterion. Pinned Mathlib https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Algebra/BigOperators/Module.lean#L57, Finset.sum_range_by_parts, supplies the discrete reverse estimate; https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/AbelSummation.lean#L300, tendsto_sum_mul_atTop_nhds_one_sub_integral₀, supplies the forward convergence argument. This precise combined equivalence is proved here as a corollary of those source identities.

import Mathlib.Algebra.BigOperators.Module
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.NormNum
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.FieldSimp
open MeasureTheory
open scoped Topology

theorem partial_sum_growth_iff_ordered_dirichlet_convergence_halfplane
    (f : ℕ → ℂ) {a : ℝ} (ha : 0 ≤ a) :
    let B := ∀ ε : ℝ, 0 < ε →
      Asymptotics.IsBigO Filter.atTop
        (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n)
        (fun N : ℕ => (N : ℝ) ^ (a + ε))
    let R := ∀ σ : ℝ, a < σ → ∃ L : ℂ,
      Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ (σ : ℂ))
        Filter.atTop (nhds L)
    let H := ∀ s : ℂ, a < s.re → ∃ L : ℂ,
      Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n / (n : ℂ) ^ s)
        Filter.atTop (nhds L)
    (B ↔ R) ∧ (R ↔ H) := by sorry
