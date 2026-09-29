-- Prove2me | Theorems.Thm_MarkovChainCLT_integral_sq_scaled_sampleAvg_le
-- name    : MarkovChainCLT.integral_sq_scaled_sampleAvg_le
-- status  : Proved
-- author  : @LukeBernese
-- created : 2026-08-16T01:28:30.660443+00:00
-- url     : https://prove2.me/theorems/b859d6f5-2fdf-4858-acbf-0af51b7493ca
-- title:
--   The normalized sample average has a second moment bounded uniformly in n
-- statement:
--   **Uniform-in-$n$ second-moment bound for the CLT-scaled sample average.** Let $P$ be a Markov kernel with invariant probability measure $\pi$, and suppose the chain has contracted to within $1/16$ in total variation after $N \ge 1$ steps, uniformly in the starting point. Then for every square-integrable observable $r$ and every $n$,
--   $$\mathbb E_\pi\Bigl[\bigl(\sqrt n\,(\bar r_n - \pi r)\bigr)^2\Bigr] \;\le\; 4N \,\operatorname{Var}_\pi(r),$$
--   where $\bar r_n = n^{-1}\sum_{k=1}^n r(X_k)$ and $\operatorname{Var}_\pi(r) = \int (r - \pi r)^2 \, d\pi$.
--
--   **Discussion.** This is the quantitative heart of the truncation argument. The bound is *uniform in $n$*, which is what allows the approximation errors to be controlled simultaneously for all $n$ - the essential hypothesis of the $3\varepsilon$ closure. It is also uniform in $r$ in the sense that the constant $4N$ depends only on the chain, so the same estimate applies to the truncated observable $f_K$, to the tail $f - f_K$, and to differences $f_K - f_L$.
--
--   Note that the right-hand side is the *variance*, not the second moment, so no centring hypothesis on $r$ is needed: the statement is invariant under adding a constant to $r$, exactly as the left-hand side is.
--
--   **Proof.** Set $c = \pi r$ and $g = r - c$. Then $g$ is measurable, square integrable (expand $g^2 = r^2 - 2cr + c^2$; $r$ itself is integrable because $r^2$ is and $\pi$ is a probability measure), and has mean zero. For $n \ge 1$,
--   $$\sqrt n\,(\bar r_n - c) = \frac1{\sqrt n}\sum_{k=1}^n g(X_k),$$
--   so the left-hand side equals $n^{-1}\,\mathbb E_\pi\bigl[(\sum_{k \le n} g(X_k))^2\bigr]$. The $O(n)$ bound on the variance of partial sums of a centred square-integrable observable gives $\mathbb E_\pi[(\sum_{k\le n} g(X_k))^2] \le 4Nn \int g^2 d\pi$; dividing by $n$ gives the claim. For $n = 0$ the left-hand side is $0$ and the right-hand side is nonnegative.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, §5; I. A. Ibragimov and Yu. V. Linnik, Independent and Stationary Sequences of Random Variables, Wolters-Noordhoff 1971, Chapter 18.

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovErgodicity
import Definitions.Def_MarkovIterKernel
import Definitions.Def_TotalVariationDist
import Mathlib.Probability.Kernel.Invariance
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Filter Finset Function MeasurableSpace MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal Topology

theorem MarkovChainCLT.integral_sq_scaled_sampleAvg_le {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) (N : ℕ) (hN : 1 ≤ N)
    (hrate : ∀ x, tvDist (iterKernel P N x) π ≤ 1 / 16)
    (r : X → ℝ) (hr : Measurable r) (hL2 : Integrable (fun x => (r x) ^ 2) π) (n : ℕ) :
    ∫ ω, (Real.sqrt n * (sampleAvg r n ω - ∫ x, r x ∂π)) ^ 2 ∂(chainMeasure P π)
      ≤ 4 * N * ∫ x, (r x - ∫ y, r y ∂π) ^ 2 ∂π := by sorry
