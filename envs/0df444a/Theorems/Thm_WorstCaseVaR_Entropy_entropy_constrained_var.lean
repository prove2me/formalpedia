-- Prove2me | Theorems.Thm_WorstCaseVaR_Entropy_entropy_constrained_var
-- name    : WorstCaseVaR.Entropy.entropy_constrained_var
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:21:08.157794+00:00
-- url     : https://prove2.me/theorems/cfc09bd9-2016-460b-bc25-f50d4d92e76f
-- title:
--   Theorem 9, p. 553 — closed form of the entropy-constrained worst-case VaR
-- statement:
--   Let $P_0 = \mathcal N(\hat x, \Gamma)$ be a Gaussian distribution on $\mathbb R^n$ with positive definite covariance $\Gamma \succ 0$, let $d \ge 0$, and let $\mathcal P_d$ be the set of probability distributions $P$ of returns with Kullback–Leibler divergence
--   $$\mathrm{KL}(P, P_0) = \int \log\frac{dP}{dP_0}\,dP \le d.$$
--   Let $w \in \mathbb R^n$ be a nonzero portfolio and $0 < \varepsilon < 1$ a loss probability level. The worst-case Value-at-Risk
--   $$V_{\mathcal P_d}(w) = \min\Big\{\gamma : \sup_{P \in \mathcal P_d} P\{\gamma \le -w^\top x\} \le \varepsilon\Big\}$$
--   exists and equals
--   $$V_{\mathcal P_d}(w) = \kappa(\varepsilon,d)\sqrt{w^\top\Gamma w} - \hat x^\top w,$$
--   where $\kappa(\varepsilon,d) = -\Phi^{-1}(f(\varepsilon,d))$, $f(\varepsilon,d) = \sup_{\lambda>0} \dfrac{e^{\varepsilon/\lambda - d} - 1}{e^{1/\lambda} - 1}$, and $\Phi$ is the standard normal cumulative distribution function.
--
--   The theorem shows that an entropy ball around a Gaussian changes the Gaussian VaR only through its risk factor: the worst-case VaR keeps the mean–standard deviation form, with $-\Phi^{-1}(\varepsilon)$ replaced by $\kappa(\varepsilon, d)$, so it can be optimised over portfolios by second-order cone programming.
--
--   **Formalization Note** "min" is encoded as `IsLeast` of the feasible set $\{\gamma : P\{\gamma \le -w^\top x\} \le \varepsilon \text{ for all } P \in \mathcal P_d\}$, and "sup over $\mathcal P_d$ is at most $\varepsilon$" as "for every $P \in \mathcal P_d$". The paper's range $\varepsilon \in (0,1]$ is narrowed to $(0,1)$: at $\varepsilon = 1$ every $\gamma$ is feasible and no minimum exists. The hypothesis $w \neq 0$ is the paper's standing assumption that the admissible set of portfolios does not contain $0$. $\|\Gamma^{1/2}w\|_2$ is written $\sqrt{w^\top \Gamma w}$, and $\Phi^{-1}(p) = \inf\{t : p \le \Phi(t)\}$.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 553, Theorem 9, Eqs. (43)-(45); p. 544, Eq. (4)

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- Theorem 9, p. 553: when the distribution of returns is only known to satisfy the relative
entropy constraint `KL(P, P₀) ≤ d` with respect to the Gaussian `P₀ = 𝒩(x̂, Γ)`, `Γ ≻ 0`,
the entropy-constrained worst-case Value-at-Risk (4) of a portfolio `w ≠ 0` at level
`ε ∈ (0, 1)` is `V_𝒫(w) = κ(ε, d)√(wᵀΓw) - x̂ᵀw` (Eq. (44)): this value is the least `γ`
with `P{γ ≤ -wᵀx} ≤ ε` for every such `P`. -/
theorem entropy_constrained_var {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 ≤ d) :
    IsLeast (varFeasible (klBall xhat Γ d) w ε)
      (kappaEntropy ε d * Real.sqrt (quadForm Γ w) - inner ℝ xhat w) := by sorry

end WorstCaseVaR.Entropy
