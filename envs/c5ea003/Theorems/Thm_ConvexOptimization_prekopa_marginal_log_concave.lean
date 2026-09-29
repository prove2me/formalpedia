-- Prove2me | Theorems.Thm_ConvexOptimization_prekopa_marginal_log_concave
-- name    : ConvexOptimization.prekopa_marginal_log_concave
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-11T21:43:54.512041+00:00
-- url     : https://prove2.me/theorems/ecd3dde6-03ff-444c-b5a0-42f7060358e1
-- title:
--   Prékopa's theorem: marginals of log-concave functions are log-concave
-- statement:
--   **Prékopa's theorem: marginals of log-concave functions are log-concave** — the goal of this mission.
--
--   Let $f : \mathbb{R}^n \times \mathbb{R}^m \to \mathbb{R}$ be measurable and log-concave, meaning $f \ge 0$ and
--
--   $$f(z_1)^{a} f(z_2)^{b} \le f(a z_1 + b z_2) \qquad \text{for all } z_1, z_2 \in \mathbb{R}^n\times\mathbb{R}^m,\ a, b \ge 0,\ a + b = 1,$$
--
--   and suppose the section $y \mapsto f(x,y)$ is integrable for every $x$. Then the marginal
--
--   $$g(x) \;=\; \int_{\mathbb{R}^m} f(x,y)\, dy$$
--
--   is log-concave on $\mathbb{R}^n$.
--
--   Integrating out variables therefore preserves log-concavity — a closure property with no analogue for most shape constraints, and one that fails, for instance, for quasi-concavity. Its consequences run through applied probability: the marginals and the convolution of log-concave densities are log-concave (so sums of independent log-concave random variables stay log-concave), the cumulative distribution function of a log-concave density is log-concave, and the probability that a random convex constraint is satisfied is a log-concave function of the parameters — the fact that makes chance-constrained programming tractable.
--
--   **Formalization Note** Log-concavity is the mission's `LogConcaveOn Set.univ` predicate in its zero-permitting power form; the marginal is a Bochner integral `∫ y, f (x, y)`, and integrability of every section is an explicit hypothesis rather than a consequence, since no decay is assumed. Source: B&V §3.5.2, pp. 106–107; Prékopa (1973), proved here via the Prékopa–Leindler inequality applied to sections.
-- source:
--   Boyd & Vandenberghe 2004, Convex Optimization, Cambridge University Press (seventh printing with corrections, 2009), https://web.stanford.edu/~boyd/cvxbook/, pp. 106-107, §3.5.2 (integration of log-concave functions; Prekopa's theorem). Original source: Prekopa 1973, On logarithmic concave measures and functions, Acta Scientiarum Mathematicarum 34, pp. 335-343. Proved via the Prekopa-Leindler inequality applied to the sections of the integrand

import Mathlib
import Definitions.Def_LogConcaveOn

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

theorem ConvexOptimization.prekopa_marginal_log_concave {n m : ℕ}
    (f : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin m) → ℝ)
    (hf_meas : Measurable f)
    (hf_lc : LogConcaveOn Set.univ f)
    (hf_int : ∀ x : EuclideanSpace ℝ (Fin n),
      Integrable (fun y : EuclideanSpace ℝ (Fin m) => f (x, y))) :
    LogConcaveOn Set.univ
      (fun x : EuclideanSpace ℝ (Fin n) =>
        ∫ y : EuclideanSpace ℝ (Fin m), f (x, y)) := by
  sorry
