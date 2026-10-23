-- Prove2me | Theorems.Thm_ZhangHager2004_thm2_2_global_convergence_faithful
-- name    : ZhangHager2004.thm2_2_global_convergence_faithful
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-23T00:29:48.17299+00:00
-- url     : https://prove2.me/theorems/4c0a3a5c-bfdb-4a4d-bc4f-ff12cde4a3d2
-- title:
--   Theorem 2.2, as stated in the paper (no descent assumption at early iterations)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be continuously differentiable and bounded below, with gradient $g(x)=\nabla f(x)$. Fix parameters $0\le\eta_{\min}\le\eta_{\max}\le1$, $0<\delta<\sigma<1<\rho$ and $\mu>0$, and let $(x_k,d_k,\alpha_k,\eta_k)_{k\ge0}$ be a run of the nonmonotone line search algorithm of Zhang and Hager: $x_{k+1}=x_k+\alpha_kd_k$, $\eta_k\in[\eta_{\min},\eta_{\max}]$, and every step $\alpha_k$ is accepted by the nonmonotone Wolfe conditions (1.4)–(1.5), or every step by the nonmonotone Armijo rule, relative to the reference values $C_k$ of (1.6) ($C_0=f(x_0)$, $Q_0=1$, $Q_{k+1}=\eta_kQ_k+1$, $C_{k+1}=(\eta_kQ_kC_k+f(x_{k+1}))/Q_{k+1}$). Assume the direction assumption: there are $c_1,c_2>0$ with
--
--   $$g_k^{\mathsf T}d_k\le-c_1\|g_k\|^2,\qquad\|d_k\|\le c_2\|g_k\|\qquad\text{for all sufficiently large }k,$$
--
--   and that $\nabla f$ is $L$-Lipschitz on the level set $\mathcal L=\{x:f(x)\le f(x_0)\}$ if the Wolfe conditions are used, and on $\bar{\mathcal L}=\{x:\operatorname{dist}(x,\mathcal L)\le\mu d_{\max}\}$, $d_{\max}=\sup_k\|d_k\|$, if the Armijo rule is used. Then
--
--   1. $\liminf_{k\to\infty}\|\nabla f(x_k)\|=0$;
--   2. if $\eta_{\max}<1$, then $\nabla f(x_k)\to0$;
--   3. if $\eta_{\max}<1$, every limit of a convergent subsequence of $(x_k)$ is a stationary point of $f$.
--
--   This is Theorem 2.2 of Zhang and Hager (2004) as printed, the global convergence result for their nonmonotone line search. The existing theorem NonmonotoneLS.Global.global_convergence proves the same conclusions under the additional hypothesis $\nabla f(x_k)d_k\le0$ for every $k$; this version imposes no sign condition on $\nabla f(x_k)d_k$ at the iterations before the direction assumption takes effect.
--
--   **Formalization Note** (1) is stated as "for every $\varepsilon>0$, $\|\nabla f(x_k)\|<\varepsilon$ for infinitely many $k$". $d_{\max}$ and the distance to $\mathcal L$ are computed in $[0,\infty]$, so unbounded directions make $\bar{\mathcal L}$ the whole space. The stopping test is not modelled: a run is an infinite sequence.
-- source:
--   Zhang, Hager, A Nonmonotone Line Search Technique and Its Application to Unconstrained Optimization, SIAM J. Optim. 14 (2004) 1043–1056, doi:10.1137/S1052623403428208, p. 1047, Theorem 2.2 (direction assumption pp. 1046–1047)

import Mathlib
import Definitions.Def_NonmonotoneLS_Shared_Params
import Definitions.Def_NonmonotoneLS_Shared_Cost
import Definitions.Def_NonmonotoneLS_Shared_Steps
import Definitions.Def_NonmonotoneLS_Global_Run
import Definitions.Def_NonmonotoneLS_Global_Regions

open scoped InnerProductSpace NNReal Topology
open Filter

theorem ZhangHager2004.thm2_2_global_convergence_faithful {n : ℕ} (p : NonmonotoneLS.Shared.Params)
    (r : NonmonotoneLS.Global.Rule)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : ContDiff ℝ 1 f) (hbdd : BddBelow (Set.range f))
    (x d : ℕ → EuclideanSpace ℝ (Fin n)) (α η : ℕ → ℝ)
    (hrun : NonmonotoneLS.Global.IsNLSARun p r f x d α η)
    (hdir : NonmonotoneLS.Global.DirectionAssumption f x d)
    (hLip : ∃ L : ℝ≥0, NonmonotoneLS.Global.LipschitzHyp p r f x d L) :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ k in atTop, ‖gradient f (x k)‖ < ε) ∧
      (p.ηmax < 1 → Tendsto (fun k => gradient f (x k)) atTop (𝓝 0)) ∧
      (p.ηmax < 1 → ∀ xstar : EuclideanSpace ℝ (Fin n),
        (∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 xstar)) →
          gradient f xstar = 0) := by sorry
