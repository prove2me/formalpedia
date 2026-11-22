-- Prove2me | Theorems.Thm_Erdos390_Full_OmittedTiltHarmonicRate_exists_uniform_omittedTilt_divInd_paper_bound_with_harmonic_rate
-- name    : Erdos390.Full.OmittedTiltHarmonicRate.exists_uniform_omittedTilt_divInd_paper_bound_with_harmonic_rate
-- status  : Proved
-- author  : @doctosil
-- created : 2026-09-17T16:53:33.374774+00:00
-- url     : https://prove2.me/theorems/c7c19a36-eeba-4206-9cc8-2f557cd11446
-- title:
--   Uniform omitted-tilt divisor law with two harmonic margins
-- statement:
--   Write $L=\log n$, $y=n^{2/9}$, $Y=\lfloor y\rfloor$, $U=9/2$, and $v_d=U-\log d/\log y$. Let $\rho$ denote the Dickman function. Fix a head pattern $H$, $0<A<C$, $B\ge0$, and integer $W>1$. There exist $K\ge0$, $c>0$, a nonnegative sequence $\epsilon$ equal to the explicit function $\mathrm{omittedTiltRemainder}(K,B,C,c,W)$, and $N_0$. Explicitly, with $M_n=\mathrm{omittedTiltMajorant}(B,C,c,W,n)$,
--
--   $$\epsilon_n=|K/L|+2|M_n|(1+1/\rho(U)+|K/L|).$$
--
--    Uniformly for $n\ge N_0$, positive $Y$-smooth $D\le Y^4$ coprime to the head modulus, prime subsets $P\subseteq(W,Y]$ coprime to $D$, and coefficients $|\eta_p|\le B$ on $P$, the structured cell $S$ with physical endpoints $\lfloor An\rfloor,\lfloor Cn\rfloor$ is nonempty. Tilt its uniform law by $L^{-1}\sum_{p\in P}\eta_p v_p(m)$. Then
--
--   $$\epsilon_n\to0,\quad\epsilon_n\log L\to0,\quad\epsilon_n(\log L)^2\to0,\qquad\left|\mathbb P_{\rm tilt}(D\mid m)-\frac{\rho(v_D)}{D\rho(U)}\right|\le\frac{\epsilon_n}{D}.$$
--
--   The explicit common remainder can be carried through later harmonic row sums without losing its uniformity.
-- source:
--   https://github.com/ShouqiaoW/erdos/blob/61325b10bbdc29f4fb5e0618b414b9f2189333ad/390/lean/Erdos390/Full/OmittedTiltHarmonicRate.lean#L418-L671

import Definitions.Def_erdos390_remaining_analytic_propositions_001
import Mathlib
import Definitions.Def_erdos390_source_bank_interface
import Definitions.Def_erdos390_dickman_step_function
import Theorems.Thm_MediumPNT
import Definitions.Def_erdos390_analytic_foundations_001
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_product_bound
import Theorems.Thm_Erdos390_Full_DickmanBasic_rho_pos_on_zero_five
import Theorems.Thm_Erdos390_Full_DickmanBasic_kernel_secondDerivative_first_bound

theorem Erdos390.Full.OmittedTiltHarmonicRate.exists_uniform_omittedTilt_divInd_paper_bound_with_harmonic_rate : Erdos390.RemainingAnalyticGoal001_005 := by sorry
