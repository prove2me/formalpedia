-- Prove2me | Theorems.Thm_nontrivial_zero_strip_of_moebius_summatory_power_bound
-- name    : nontrivial_zero_strip_of_moebius_summatory_power_bound
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T02:45:50.048467+00:00
-- url     : https://prove2.me/theorems/95fedb98-81ed-4441-8558-e264323cd221
-- title:
--   A Moebius partial-sum bound confines nontrivial zeta zeros to a symmetric strip
-- statement:
--   Let $r\ge0$ and assume the signed Moebius partial sums satisfy $M(N)=\sum_{n\le N}\mu(n)=O(N^r)$. Every nontrivial zero $s$ of the Riemann zeta function then satisfies
--
--   $$1-r\le\operatorname{Re}s\le r.$$
--
--   This is a quantitative conditional zero-location theorem. It does not prove the assumed cancellation bound. In particular, a bound with exponent at most one half would imply RH; that stronger fixed-exponent estimate is not asserted to be equivalent to RH.
-- source:
--   Derived corollary of signed Abel-Mellin continuation and the zeta functional equation, rather than a verbatim textbook claim. Pinned Mathlib: https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/MellinTransform.lean#L401, mellin_differentiableAt_of_isBigO_rpow; https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/RiemannZeta.lean#L106, completedRiemannZeta_one_sub; https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/Nonvanishing.lean#L411, riemannZeta_ne_zero_of_one_le_re. Context: E. C. Titchmarsh, The Theory of the Riemann Zeta-function, second edition revised by D. R. Heath-Brown (1986), Section 14.25(A), p. 369, and the analytic-continuation paragraph preceding 14.25(B), p. 370. https://sites.math.rutgers.edu/~zeilberg/EM18/TitchmarshZeta.pdf.

import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.Analysis.MellinTransform
open MeasureTheory
open scoped Topology

theorem nontrivial_zero_strip_of_moebius_summatory_power_bound
    {r : ℝ} (hr : 0 ≤ r)
    (hM : Asymptotics.IsBigO Filter.atTop
      (fun N : ℕ => ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ))
      (fun N : ℕ => (N : ℝ) ^ r))
    {s : ℂ} (hz : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * (↑n + 1)) (h1 : s ≠ 1) :
    1 - r ≤ s.re ∧ s.re ≤ r := by sorry
