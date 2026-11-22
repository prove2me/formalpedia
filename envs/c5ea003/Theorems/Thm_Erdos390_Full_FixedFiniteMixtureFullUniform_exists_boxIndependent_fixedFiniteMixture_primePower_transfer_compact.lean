-- Prove2me | Theorems.Thm_Erdos390_Full_FixedFiniteMixtureFullUniform_exists_boxIndependent_fixedFiniteMixture_primePower_transfer_compact
-- name    : Erdos390.Full.FixedFiniteMixtureFullUniform.exists_boxIndependent_fixedFiniteMixture_primePower_transfer_compact
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T17:12:00.657407+00:00
-- url     : https://prove2.me/theorems/43dd7845-cebb-4b12-bbe2-ff57d0afe283
-- title:
--   Uniform prime-power transfer for a fixed finite family of tilted cells
-- statement:
--   For a finite bounded valuation law, write $I_{p,r}=1_{p^r\mid m}$, $I_p=I_{p,1}$, $V_p=v_p(m)$, and $J_p=V_p-I_p$. Write $t_p=\log p/\log y(n)$ and let all prime sums range over the moving band $\mathcal P_{n,W}$. The five prime-power transfer estimates with constants $(C,R)$ mean: the sums of absolute covariances of $(I_{p,r},I_q)$, $(I_p,I_{q,s})$, and $(I_{p,r},I_{q,s})$ over higher exponents have bounds $(Ct_pt_q+R)/(p^2q)$, $(Ct_pt_q+R)/(pq^2)$, and $(Ct_pt_q+R)/(p^2q^2)$, respectively; also $\mathbb E J_p^2\le(C+R)/p^2$ and $p\sum_q|\operatorname{Cov}(V_p,V_q)-\operatorname{Cov}(I_p,I_q)|\le C/W+R$. Higher exponents run from $2$ to the valuation cutoff determined by the value bound $M$. Fix finitely many head patterns $H_c$ and real endpoints $0<A_c<C_c\le C_{\max}$ with $C_{\max}>0$. The source constant $C_*$, called the box-independent prime-power constant, is positive. For every $W>1$ containing all head primes, and every coefficient bound $B\ge0$, there exist a nonnegative error sequence $\epsilon_{B,W}$ and a threshold $N_0$ such that
--   $$\epsilon_{B,W}(n)\to0,\qquad \epsilon_{B,W}(n)\log\log n\to0.$$
--   For every $n\ge N_0$ and every tilt coefficient function $|\eta_p|\le B$ on the moving prime band, the structured cells with head $H_c$, physical endpoints $A_c,C_c$, and smoothness cutoff $y_{\mathbb N}(n)$ are nonempty. Tilt their uniform laws by the valuation score normalized by $\log n$, and place their values under the common bound associated to $C_{\max}$. Every probability mixture of these laws satisfies the five transfer estimates with $(C_*,\epsilon_{B,W}(n))$. The constant $C_*$ is selected before $W$ and $B$; the error and threshold may depend on them. The moving prime band is $\{p\text{ prime}:W<p\le\lfloor n^{2/9}\rfloor\}$.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/FixedFiniteMixtureFullUniform.lean#L81-L697

import Definitions.Def_erdos390_remaining_analytic_propositions_001

universe u_1

theorem Erdos390.Full.FixedFiniteMixtureFullUniform.exists_boxIndependent_fixedFiniteMixture_primePower_transfer_compact : Erdos390.RemainingAnalyticGoal001_001.{u_1} := by sorry
