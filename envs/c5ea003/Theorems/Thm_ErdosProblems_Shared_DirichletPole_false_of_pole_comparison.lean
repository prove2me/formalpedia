-- Prove2me | Theorems.Thm_ErdosProblems_Shared_DirichletPole_false_of_pole_comparison
-- name    : ErdosProblems.Shared.DirichletPole.false_of_pole_comparison
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-25T00:53:50.111478+00:00
-- url     : https://prove2.me/theorems/15edd758-72b8-4406-9485-a8764820bdba
-- title:
--   Lean source theorem: false_of_pole_comparison
-- statement:
--   For nonnegative sequences satisfying the stated Dirichlet-convolution comparison, a uniformly bounded weighted partial sum for b, and nonzero finite residue limits for the Dirichlet series of a and m at s=1, the combined hypotheses are contradictory.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Shared/DirichletPoleComparison.lean#L157-L205
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

import Definitions.Def_ErdosProblems_Shared_DirichletPoleComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# Two simple poles exclude a squared comparison of Dirichlet series

Let `a, g, b, m : ℕ → ℝ` be nonnegative with

* `a ≤ g ⋆ b` and `g ⋆ g ≤ m` coefficientwise (Dirichlet convolution, `n ≠ 0`),
* `g ≤ a`, and the partial sums of `∑ b(n) / n` bounded by `B`.

If the Dirichlet series of `a` and of `m` both have a simple pole at `s = 1`
(`(s - 1) L(a, s) → r_a > 0` and `(s - 1) L(m, s) → r_m ≠ 0` as `s → 1⁺`), this is
impossible.  Indeed, for real `s > 1` near `1`,

`L(a, s) ^ 2 ≤ (L(g, s) L(b, s)) ^ 2 ≤ B ^ 2 L(g ⋆ g, s) ≤ B ^ 2 L(m, s)`,

so `((s - 1) L(a, s)) ^ 2 ≤ B ^ 2 (s - 1) · (s - 1) L(m, s)`; the left side tends to
`r_a ^ 2 > 0` and the right side to `0`.

This is the analytic core of the classical proof that a non-square element of a number
field is a non-square modulo infinitely many degree-one primes: `a` counts the ideals of
the base field, `m` those of the quadratic extension, `g` the ideals built from split
degree-one primes and `b` the rest.  Summability of the two series near `s = 1` is not
assumed: it follows from the nonzero limits, since a divergent series has `tsum = 0`.
-/

noncomputable section


open Filter Topology
open scoped LSeries.notation

open ErdosProblems.Shared.DirichletPole

theorem ErdosProblems.Shared.DirichletPole.false_of_pole_comparison {a g b m : ℕ → ℝ}
    (ha : ∀ n, 0 ≤ a n) (hg : ∀ n, 0 ≤ g n) (hb : ∀ n, 0 ≤ b n)
    (hga : ∀ n, g n ≤ a n)
    (h1 : ∀ n, n ≠ 0 → a n ≤ dconv g b n)
    (h2 : ∀ n, n ≠ 0 → dconv g g n ≤ m n)
    (B : ℝ) (h3 : ∀ X : ℕ, ∑ n ∈ Finset.range X, b n / n ≤ B)
    {ra rm : ℝ} (hra : 0 < ra) (hrm : rm ≠ 0)
    (hA : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * LSeries (fun n => (a n : ℂ)) s)
      (𝓝[>] 1) (𝓝 (ra : ℂ)))
    (hM : Tendsto (fun s : ℝ => ((s : ℂ) - 1) * LSeries (fun n => (m n : ℂ)) s)
      (𝓝[>] 1) (𝓝 (rm : ℂ))) :
    False := by sorry
