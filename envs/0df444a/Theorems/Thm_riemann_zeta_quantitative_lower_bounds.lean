-- Prove2me | Theorems.Thm_riemann_zeta_quantitative_lower_bounds
-- name    : riemann_zeta_quantitative_lower_bounds
-- status  : Proved
-- author  : @ryanshin
-- created : 2026-09-05T04:51:48.269654+00:00
-- url     : https://prove2.me/theorems/4adf708c-0e0c-4810-97b9-7d6743504791
-- title:
--   Conditional and unconditional quantitative lower bounds for the Riemann zeta function
-- statement:
--   Two quantitative nonvanishing estimates for the Riemann zeta function are proved together.
--
--   First, if $r\ge0$, $C>0$, and the signed Moebius sums satisfy $|M(N)|\le CN^r$ for every $N\ge1$, then for $\sigma=\operatorname{Re}s>r$ and $s\ne1$,
--
--   $$|\zeta(s)|\ge\frac{\sigma-r}{C|s|}.$$
--
--   Second, without any cancellation hypothesis, for every $\sigma=\operatorname{Re}s>1$,
--
--   $$|\zeta(s)|\ge\frac{\sigma-1}{\sigma}.$$
--
--   The second bound is uniform in the imaginary part. The first is conditional on the explicitly stated Moebius bound; neither assertion establishes RH or supplies a new cancellation estimate.
-- source:
--   Derived lower-bound corollaries of the Moebius reciprocal identity, pinned Mathlib https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/Dirichlet.lean#L319, LSeries_one_mul_Lseries_moebius; coefficient majorization https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/NumberTheory/LSeries/Basic.lean#L120, LSeries.norm_term_le; and the analytic identity theorem https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Analytic/Uniqueness.lean#L223. The conditional bound uses the signed Mellin-integral estimate proved from https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/SpecialFunctions/ImproperIntegrals.lean#L172. These displayed estimates are derived here, not claimed as verbatim theorems in those sources.

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

theorem riemann_zeta_quantitative_lower_bounds :
    (∀ (r C : ℝ), 0 ≤ r → 0 < C →
      (∀ N : ℕ, 1 ≤ N →
        ‖∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℂ)‖ ≤
          C * (N : ℝ) ^ r) →
      ∀ s : ℂ, r < s.re → s ≠ 1 →
        (s.re - r) / (C * ‖s‖) ≤ ‖riemannZeta s‖) ∧
    (∀ s : ℂ, 1 < s.re → (s.re - 1) / s.re ≤ ‖riemannZeta s‖) := by sorry
