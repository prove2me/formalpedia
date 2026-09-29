-- Prove2me | Definitions.Def_ErdosProblems_Shared_DirichletPoleComparison
-- name    : ErdosProblems_Shared_DirichletPoleComparison
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:56:52.94614+00:00
-- url     : https://prove2.me/theorems/030b60f5-16ba-4230-b374-139bd7b97423
-- title:
--   Dirichlet terms and convolution
-- statement:
--   Defines rterm for a real sequence and real parameter, and dconv for two real sequences.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/4fe59e0191169606942baae0949365070b7f419c/ErdosProblems/Shared/DirichletPoleComparison.lean#L1-L207
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1-L58
--   Paper's AI-assistance disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Original Erdős problem and Koizumi prior work are distinguished in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L57-L110

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

namespace ErdosProblems.Shared.DirichletPole

open Filter Topology
open scoped LSeries.notation

/-- The real term `f n / n ^ s` of a Dirichlet series, with the `n = 0` term removed. -/
def rterm (f : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else f n / (n : ℝ) ^ s

/-- Dirichlet convolution of real sequences. -/
def dconv (f g : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ x ∈ n.divisorsAntidiagonal, f x.1 * g x.2























end ErdosProblems.Shared.DirichletPole


