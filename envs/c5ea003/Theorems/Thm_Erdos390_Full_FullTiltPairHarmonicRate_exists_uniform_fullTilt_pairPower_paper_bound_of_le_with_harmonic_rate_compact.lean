-- Prove2me | Theorems.Thm_Erdos390_Full_FullTiltPairHarmonicRate_exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate_compact
-- name    : Erdos390.Full.FullTiltPairHarmonicRate.exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:10:08.547906+00:00
-- url     : https://prove2.me/theorems/9a6a7450-3428-4627-9965-543a4d789786
-- title:
--   Full two-prime valuation tilt with harmonic-rate remainder
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Fix a head pattern $H$, $0<A<C$, $B\ge0$, and integer $W>1$. There exist a nonnegative sequence $\epsilon_n$ with $\epsilon_n$, $\epsilon_n\log L$, and $\epsilon_n(\log L)^2$ tending to zero, and a uniform threshold $N_0$. For $n\ge N_0$, distinct band primes $p,q$ coprime to the head modulus, $D=p^rq^s\le Y^4$, and coefficients bounded by $B$ on the whole prime band, the structured cell is nonempty. Tilt its uniform law by the full band valuation score. Put $m_D=\rho(v_D)/(D\rho(U))$, and let $R_{r,s}$ be the two-local restoration error with actual valuation cutoffs and the prescribed pair fallback constant.
--
--   $$|\mathbb P_{\rm full\ tilt}(D\mid m)-m_D|\le 2\left(R_{r,s}+\frac{\epsilon_n}{D}+|m_D|R_{0,0}\right).$$
--
--   This supplies the actual full-valuation two-prime chamber estimate, with a remainder strong enough for two harmonic losses.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/FullTiltPairHarmonicRate.lean#L26-L186

import Definitions.Def_erdos390_remaining_analytic_propositions_001

theorem Erdos390.Full.FullTiltPairHarmonicRate.exists_uniform_fullTilt_pairPower_paper_bound_of_le_with_harmonic_rate_compact : Erdos390.RemainingAnalyticGoal001_004 := by sorry
