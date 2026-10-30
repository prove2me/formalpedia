-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch9_LimitLaws_RCyclesPoissonNS_Multivariate_multivariateLaw_tendsto_poissonPi
-- name    : AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Multivariate.multivariateLaw_tendsto_poissonPi
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-26T18:48:43.167649+00:00
-- url     : https://prove2.me/theorems/aaa5b586-ced2-47a0-9313-1139cd08eeb8
-- title:
--   Independent Poisson limit for fixed distinct permutation-cycle lengths
-- statement:
--   Fix a natural dimension $m$ and an injective map $\ell:\operatorname{Fin}(m)\to\mathbb N$ with $\ell(i)>0$ for every $i$. For each $n$, choose one uniform permutation $\sigma_n$ of $\{0,\ldots,n-1\}$ and form its simultaneous cycle-count vector
--
--   $$\mathbf C_n=(C_{\ell(i)}(\sigma_n))_{i\in\operatorname{Fin}(m)}.$$
--
--   Its pushforward probability measure on $\mathbb N^{\operatorname{Fin}(m)}$ converges in the weak topology to
--
--   $$\mathcal L(\mathbf C_n)\longrightarrow\bigotimes_{i\in\operatorname{Fin}(m)}\operatorname{Poisson}(1/\ell(i)).$$
--
--   The positive cycle lengths are pairwise distinct, and both the dimension and every length remain fixed in the limit. Independence describes the finite product limit, not the finite-$n$ coordinates, which all come from the same permutation. Fixed points are included when a chosen length is $1$. The case $m=0$ is the well-defined empty-vector/product law. No infinite-dimensional or process convergence, varying dimension/lengths, rate or total-variation conclusion is asserted. Positivity and injectivity are the only public hypotheses; the exact joint-count and mixed-moment formulas are proved source inputs.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch9/LimitLaws/MultivariateCyclePoisson.lean#L797. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch9_LimitLaws_MultivariateCyclePoisson
import Mathlib
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Combinatorics.Derangements.Exponential
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Multivariate Poisson limits for finitely many cycle counts

This file contains the finite-product discrete bridge and the basic singleton
mass identities for vectors of cycle counts.
-/

open Filter MeasureTheory
open scoped Topology ENNReal NNReal

open AnalyticCombinatorics
open AnalyticCombinatorics.Ch9
open AnalyticCombinatorics.Ch9.LimitLaws
open AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS
open AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Multivariate

-- The finite-product `HasSum` induction combines a dependent tail series with
-- `HasSum.mul`; the local heartbeat bump prevents a deterministic timeout in
-- the summability witness elaboration.

theorem AnalyticCombinatorics.Ch9.LimitLaws.RCyclesPoissonNS.Multivariate.multivariateLaw_tendsto_poissonPi {m : ℕ} (lengths : Fin m → ℕ)
    (hpos : ∀ i : Fin m, 0 < lengths i) (hinj : Function.Injective lengths) :
    Tendsto (fun n : ℕ => multivariateLaw n lengths) atTop
      (𝓝 (poissonPiMeasure lengths)) := by sorry
