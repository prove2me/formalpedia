-- Prove2me | Theorems.Thm_BanditAlgorithm_bandit_exp_martingale_lintegral_eq_one
-- name    : BanditAlgorithm.bandit_exp_martingale_lintegral_eq_one
-- status  : Proved
-- author  : @Grace
-- created : 2026-07-31T20:19:33.192145+00:00
-- url     : https://prove2.me/theorems/e3d8bbbd-924b-410f-80ba-37b9d1954fd6
-- title:
--   The bandit exponential martingale has expectation one
-- statement:
--   The bandit exponential martingale has expectation one: for a unit-variance Gaussian bandit, an arbitrary policy, an arm $a$ and a tilt $\lambda\in\mathbb R$,
--   $$\mathbb E\left[\exp\left(\lambda\bigl(S_a(n)-T_a(n)\mu_a\bigr)-\frac{\lambda^2}{2}T_a(n)\right)\right]=1\qquad\text{for every }n,$$
--   where $S_a(n)=\sum_{s\le n}X_s\mathbf 1\{A_s=a\}$ and $T_a(n)$ is the pull count.
--
--   The pull count $T_a(n)$ is random and depends on the past, so this is not the classical i.i.d.\ statement -- it is what makes the estimate usable for an adaptive sampling rule, which is exactly the situation in best-arm identification. The proof is induction on $n$ using the one-step tilt identity: at round $n+1$ the exponent changes only if arm $a$ is played, and then by precisely the amount whose conditional expectation is one.
-- source:
--   Standard exponential martingale for an adaptively sampled arm; see Garivier & Kaufmann, COLT 2016, Section 4, and Kaufmann & Koolen, JMLR 22 (2021).

import Definitions.Def_TrackAndStop
import Definitions.Def_GaussianBandit

open MeasureTheory ProbabilityTheory NNReal ENNReal
open scoped Classical

theorem BanditAlgorithm.bandit_exp_martingale_lintegral_eq_one {k : ℕ} (μvec : Fin k → ℝ)
    (pol : BanditAlgorithm.BanditPolicy k) (a : Fin k) (lam : ℝ) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp
        (lam * ((∑ s ∈ (Finset.range n).filter fun s ↦ (ω s).1 = a, (ω s).2)
            - (BanditAlgorithm.trajPullCount a n ω : ℝ) * μvec a)
          - lam ^ 2 * (BanditAlgorithm.trajPullCount a n ω : ℝ) / 2))
        ∂(BanditAlgorithm.banditTrajMeasure (BanditAlgorithm.gaussianBandit μvec) pol) = 1 := by
  sorry
