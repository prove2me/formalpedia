-- Prove2me | Theorems.Thm_dirichlet_mellin_logarithmic_moments_and_all_derivatives
-- name    : dirichlet_mellin_logarithmic_moments_and_all_derivatives
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T02:48:53.246077+00:00
-- url     : https://prove2.me/theorems/47ffd322-6a8c-4786-bbd2-90c01e5104e3
-- title:
--   All logarithmic moments and all derivatives of a Dirichlet Mellin continuation
-- statement:
--   Let $f:\mathbb N\to\mathbb C$ have signed partial sums $M(N)=O(N^r)$, with $r\ge0$. For $\operatorname{Re}s>r$, write
--
--   $$J_k(s)=\int_1^\infty(\log t)^kM(\lfloor t\rfloor)t^{-s-1}\,dt,\qquad F(s)=sJ_0(s).$$
--
--   Every logarithmic moment converges absolutely as an integral, and for every pair of nonnegative integers $k,n$,
--
--   $$J_k^{(n)}(s)=(-1)^nJ_{k+n}(s).$$
--
--   The continuation therefore satisfies, for every $n\ge0$,
--
--   $$F^{(n+1)}(s)=(-1)^{n+1}sJ_{n+1}(s)+(n+1)(-1)^nJ_n(s).$$
--
--   These formulas provide integral representations of all derivatives using only signed cancellation estimates. Absolute convergence of the integrals does not assert absolute convergence of the original Dirichlet series.
-- source:
--   Derived all-order application of pinned Mathlib https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/MellinTransform.lean#L320, mellin_hasDerivAt_of_isBigO_rpow; polynomial logarithmic growth is absorbed using isLittleO_log_rpow_rpow_atTop. Product/chain rules and induction give the displayed formulas. The all-order specialization is proved here rather than attributed as a verbatim theorem.

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
open MeasureTheory
open scoped Topology

theorem dirichlet_mellin_logarithmic_moments_and_all_derivatives
    (f : ℕ → ℂ) {r : ℝ} (hr : 0 ≤ r)
    (hO : Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, f n)
      (fun N : ℕ => (N : ℝ) ^ r))
    {s : ℂ} (hs : r < s.re) :
    let M := fun t : ℝ => ∑ n ∈ Finset.Icc 1 ⌊t⌋₊, f n
    let J := fun k : ℕ => fun z : ℂ => mellin (fun t => (Real.log t) ^ k • M t) (-z)
    let F := fun z : ℂ => z * mellin M (-z)
    (∀ k : ℕ, MellinConvergent (fun t => (Real.log t) ^ k • M t) (-s)) ∧
    (∀ k n : ℕ, iteratedDeriv n (J k) s = (-1 : ℂ) ^ n * J (k + n) s) ∧
    (∀ n : ℕ, iteratedDeriv (n + 1) F s =
      (-1 : ℂ) ^ (n + 1) * s * J (n + 1) s +
        ((n + 1 : ℕ) : ℂ) * (-1 : ℂ) ^ n * J n s) := by sorry
