-- Prove2me | Theorems.Thm_Erdos390_Full_PaperBridgeFit_BridgeData_eventually_exists_uniform_actualBandSchurEquiv_and_quadratic_compact
-- name    : Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:04:03.962513+00:00
-- url     : https://prove2.me/theorems/5614e89a-a552-4134-94ad-ee840f72ee7c
-- title:
--   Eventual uniform Schur inverse and quadratic lower bound
-- statement:
--   Write $L_n=\log n$, $y_n=n^{2/9}$, $Y_n=\lfloor y_n\rfloor$, and $\mathcal P_{n,W}=\{p\text{ prime}:W<p\le Y_n\}$. Fix nonempty finite head and band sets, physical intervals with $1\le I_\sigma^{\rm lower}<I_\sigma^{\rm upper}\le U$, $U\ge1$, a cutoff $W>1$, radius $a\ge0$, and constants $m_0,s,C_f>0$. Let $\epsilon_n\ge0$ satisfy $\epsilon_n\log L_n\to0$. Eventually in $n$, consider any bridge of size $n$ and cutoff $W$ with these physical endpoints and a barycentric target of cell-mass margin at least $m_0$ supplying its baseline. Suppose that throughout the effective ball $\|z\|\le a$ its full projected operator is a continuous linear equivalence with inverse norm at most $C_f$, every band center is at least $s/\log L_n$, and every nuisance-valuation covariance is at most $\epsilon_n/p$ in absolute value. Set $\gamma$ to the canonical nuisance gap for $I,U,3a$ and the target, $r$ to the source nuisance marked Schur rate at $(\epsilon_n,\gamma,s/\log L_n)$, and $C_s=C_f/(1-2C_fr)$. For every point in the ball, the actual band Schur operator $S_z$ is a linear equivalence, and
--
--   $$\|S_z^{-1}v\|_\sharp\le C_s\|v\|_\sharp,\qquad C_s\le2C_f,$$
--   $$\frac{d_{\min}^2}{\Omega C_s}\|q\|_\sharp^2\le\operatorname{Var}_{\mu_z}(\operatorname{Res}_{\rm nuis}Q_q).$$
--
--   Here $\|\cdot\|_\sharp$ is the paper sharp norm, $d_{\min}$ is the source raw diagonal lower weight, $\Omega$ is total sharp weight, and $Q_q$ is the full band-regression score.
--
--   The eventual threshold is uniform in all later bridges and inverse families, and the retained inverse constant is at most twice the full inverse constant.
--
--   This compact declaration is definitionally identical to the original fully quantified statement; the named proposition preserves every hypothesis.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/PaperSelectedMeshSchurEventually.lean#L29-L224

import Definitions.Def_erdos390_analytic_compact_goals

universe u_1 u_2

theorem Erdos390.Full.PaperBridgeFit.BridgeData.eventually_exists_uniform_actualBandSchurEquiv_and_quadratic_compact : Erdos390.AnalyticCompactGoal002.{u_1, u_2} := by sorry
