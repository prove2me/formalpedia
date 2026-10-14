-- Prove2me | Theorems.Thm_syracuse_uniform_logarithmic_tail_bound_ge_three
-- name    : syracuse_uniform_logarithmic_tail_bound_ge_three
-- status  : Open
-- author  : @mysticflounder
-- created : 2026-10-12T22:43:42.479986+00:00
-- url     : https://prove2.me/theorems/10697865-c049-4b18-8190-6f57f19040fc
-- title:
--   Tao Theorem 3.1 for thresholds at least three: uniform logarithmic tail bound
-- statement:
--   There are absolute positive constants $C$ and $c$ such that, for every real threshold $M \ge 3$ and every real cutoff $x \ge 2$, the sum of $1/n$ over positive odd integers $n \le x$ whose full Syracuse orbit minimum exceeds $M$, divided by $\log x$, is at most $C/(\log M)^c$:
--
--   $$\frac{1}{\log x}\sum_{\substack{n \le x,\ n\ \mathrm{odd},\ \mathrm{Syr}_{\min}(n) > M}} \frac{1}{n} \le \frac{C}{(\log M)^c}.$$
--
--   Both constants are independent of $M$ and $x$, and the orbit includes its initial value.
--
--   This is Theorem 3.1 of Tao's paper restricted to thresholds $M \ge 3$. The restriction loses no content: the proof of Theorem 3.1 begins by observing that bounded thresholds are trivial from a uniform bound on the total normalized mass, so one may assume the threshold exceeds any fixed absolute constant. All of the analytic content of Theorem 3.1 (stabilization of first passage, via the 2-adic valuation distribution and 3-adic fine-scale mixing) is contained in this large-threshold form.
--
--   **Formalization Note** The orbit minimum is `syracuseOrbitMin` and the normalized sum is `weightedLogMassReal`, exactly as in the unrestricted Theorem 3.1 statement `syracuse_uniform_logarithmic_tail_bound`.
-- source:
--   Terence Tao, Almost all orbits of the Collatz map attain almost bounded values, Forum of Mathematics, Pi 10 (2022), e12; arXiv:1909.03562v7, Theorem 3.1, first displayed estimate, restricted to N0 >= 3 following the first paragraph of its proof in Section 3. https://arxiv.org/html/1909.03562v7

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_weightedLogMassReal
import Definitions.Def_syracuseOrbitMin

theorem syracuse_uniform_logarithmic_tail_bound_ge_three :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ M x : ℝ, 3 ≤ M → 2 ≤ x →
      weightedLogMassReal (fun n => 0 < n ∧ Odd n)
        (fun n => M < (syracuseOrbitMin n : ℝ)) (fun n => 1 / (n : ℝ)) x
        ≤ C / Real.rpow (Real.log M) c := by sorry
