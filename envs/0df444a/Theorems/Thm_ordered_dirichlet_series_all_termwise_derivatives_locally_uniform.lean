-- Prove2me | Theorems.Thm_ordered_dirichlet_series_all_termwise_derivatives_locally_uniform
-- name    : ordered_dirichlet_series_all_termwise_derivatives_locally_uniform
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T02:48:48.882531+00:00
-- url     : https://prove2.me/theorems/d5b238d7-8f74-4c11-87b4-d6fee9f605db
-- title:
--   Locally uniform termwise differentiation of a Dirichlet series at every order
-- statement:
--   Let $f:\mathbb N\to\mathbb C$ have signed partial sums $M(N)=O(N^r)$, with $r\ge0$, and let $F$ be its analytic Mellin continuation on $\operatorname{Re}s>r$. For every integer $j\ge0$,
--
--   $$\sum_{n=1}^N\frac{f(n)(-\log n)^j}{n^s}\longrightarrow F^{(j)}(s)\quad\text{locally uniformly on }\operatorname{Re}s>r.$$
--
--   This justifies differentiation term by term to every order despite the absence of an absolute-convergence hypothesis on the Dirichlet series. For positive integers the complex logarithm in the formal statement equals the ordinary real logarithm.
-- source:
--   Derived application of the Weierstrass differentiation theorem, pinned Mathlib https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Complex/LocallyUniformLimit.lean#L154, TendstoLocallyUniformlyOn.deriv, combined with the signed local-uniform convergence result proved here from the identities in https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/AbelSummation.lean. All-order differentiation is obtained by induction.

import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.NormNum
open MeasureTheory
open scoped Topology

theorem ordered_dirichlet_series_all_termwise_derivatives_locally_uniform
    (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n)
      (fun N : ℕ => (N : ℝ) ^ r)) (j : ℕ) :
    TendstoLocallyUniformlyOn
      (fun N : ℕ => fun s : ℂ => ∑ n ∈ Finset.Icc 1 N,
        f n * (-Complex.log (n : ℂ)) ^ j / (n : ℂ) ^ s)
      (iteratedDeriv j (fun s : ℂ =>
        s * mellin (fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n) (-s)))
      Filter.atTop {s : ℂ | r < s.re} := by sorry
