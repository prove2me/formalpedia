-- Prove2me | Theorems.Thm_Erdos390_Full_FixedFiniteMixtureLemma75_sigmaMixture_primePowerTransferBounds_of_common_profiles_compact
-- name    : Erdos390.Full.FixedFiniteMixtureLemma75.sigmaMixture_primePowerTransferBounds_of_common_profiles_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:10:01.160496+00:00
-- url     : https://prove2.me/theorems/d5845081-b5d5-4336-8b66-365ead9ea0a7
-- title:
--   Common marked profiles imply the finite-mixture prime-power estimates
-- statement:
--   For a finite bounded valuation law, write $I_{p,r}=1_{p^r\mid m}$, $I_p=I_{p,1}$, $V_p=v_p(m)$, and $J_p=V_p-I_p$. Write $t_p=\log p/\log y(n)$ and let all prime sums range over the moving band $\mathcal P_{n,W}$. The five prime-power transfer estimates with constants $(C,R)$ mean: the sums of absolute covariances of $(I_{p,r},I_q)$, $(I_p,I_{q,s})$, and $(I_{p,r},I_{q,s})$ over higher exponents have bounds $(Ct_pt_q+R)/(p^2q)$, $(Ct_pt_q+R)/(pq^2)$, and $(Ct_pt_q+R)/(p^2q^2)$, respectively; also $\mathbb E J_p^2\le(C+R)/p^2$ and $p\sum_q|\operatorname{Cov}(V_p,V_q)-\operatorname{Cov}(I_p,I_q)|\le C/W+R$. Higher exponents run from $2$ to the valuation cutoff determined by the value bound $M$. Let a finite family of bounded valuation laws have arbitrary probability mixture weights. Suppose $n,W>1$; all constants $C_K,\epsilon,G_0,k,G_f,T_\ell,T_q,T_d,T_r$ are nonnegative; and the four-mark profile $F$ satisfies $|F(x+z)-F(x)F(z)|\le C_Kxz$ for $x,z\ge0$, $x+z\le4$. In every component assume one- and two-prime divisibility expectations differ from the common paper main term by at most $E_P(r+1)/p^r$ and $E_P(r+1)(s+1)/(p^rq^s)$ whenever the divisor is at most $y_{\mathbb N}(n)^4$, where $E_P$ is the source's restored probability scale $\operatorname{pairProbabilityScale}(\epsilon,G_0,k)$. Assume also $\mathbb P(D\mid m)\le G_f/D$ for every positive $D$. The resulting outside-chamber residuals must satisfy the linear, quadratic, diagonal, and row budgets $T_\ell,T_q,T_d,T_r$ of the finite aggregation theorem, and $\sum_p t_p/p\le2\log4$. Then
--   $$\operatorname{TransferBounds}(\mu_{\rm mix};n,W,C_{\rm paper}(C_K),\operatorname{genericAggregationRemainder}(E_A,T_\ell,T_q,T_d,T_r;n,W)),$$
--   where $E_A=\operatorname{primePowerChamberRemainder}(\epsilon,G_0,k)$ and $C_{\rm paper}$ is the fixed paper prime-power constant. Thus the five estimates include the full between-component covariance. Explicitly, $C_{\rm paper}(C_K)=A_{\rm agg}(2C_K+1/\rho(U))(2\log4+5)$; the generic remainder is $A_{\rm agg}E_A+T_\ell+T_q+T_d+A_{\rm agg}E_A(\sum_p1/p+5)/W+T_r$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/FixedFiniteMixtureLemma75.lean#L33-L176

import Definitions.Def_erdos390_remaining_analytic_propositions_001

universe u_1 u_2

theorem Erdos390.Full.FixedFiniteMixtureLemma75.sigmaMixture_primePowerTransferBounds_of_common_profiles_compact : Erdos390.RemainingAnalyticGoal001_002.{u_1, u_2} := by sorry
