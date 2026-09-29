-- Prove2me | Theorems.Thm_WorstCaseVaR_Entropy_dual_constraint_iff
-- name    : WorstCaseVaR.Entropy.dual_constraint_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:20:06.093673+00:00
-- url     : https://prove2.me/theorems/6d9630ac-42ab-4dcb-a39a-744e19643a7f
-- title:
--   p. 554 — the dual constraint is equivalent to γ ≥ κ(ε, d)√(wᵀΓw) − wᵀx̂
-- statement:
--   Let $\Gamma \succ 0$, $w \in \mathbb R^n$ nonzero, $0 < \varepsilon < 1$, $d > 0$ and $\gamma \in \mathbb R$, and let $\phi(\gamma) = 1 - \Phi\big((\gamma + w^\top\hat x)/\sqrt{w^\top\Gamma w}\big)$. Then there exists $\lambda > 0$ with
--   $$\lambda d + \lambda \log\big((e^{1/\lambda} - 1)\phi(\gamma) + 1\big) \le \varepsilon$$
--   if and only if
--   $$\gamma \ge \kappa(\varepsilon,d)\sqrt{w^\top\Gamma w} - w^\top \hat x,$$
--   where $\kappa(\varepsilon,d) = -\Phi^{-1}(f(\varepsilon,d))$ is the risk factor of Eq. (45).
--
--   This is the last step of the proof of Theorem 9: it inverts the constraint "worst-case probability at most $\varepsilon$" into an explicit lower bound on the loss level $\gamma$.
--
--   **Formalization Note** The paper states the loss level as $\varepsilon \in (0,1]$; at $\varepsilon = 1$ every $\gamma$ is feasible and the equivalence fails, so $\varepsilon < 1$ is assumed. The equivalence also needs $d > 0$: for $d = 0$ the supremum in (45) is approached only as $\lambda \to \infty$, so the left side means $\phi(\gamma) < \varepsilon$ while the right side means $\phi(\gamma) \le \varepsilon$, and the two differ at one value of $\gamma$. Theorem 9 itself holds for $d \ge 0$.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 554, end of the proof of Theorem 9

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- End of the proof of Theorem 9, p. 554: for `d > 0` and `0 < ε < 1`, there is `λ > 0` with
`λd + λ log((e^{1/λ} - 1)φ(γ) + 1) ≤ ε` if and only if `γ ≥ κ(ε, d)√(wᵀΓw) - wᵀx̂`. -/
theorem dual_constraint_iff {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (ε d : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hd : 0 < d) (γ : ℝ) :
    (∃ lam > 0, dualValue d (gaussianTail xhat Γ w γ) lam ≤ ε) ↔
      kappaEntropy ε d * Real.sqrt (quadForm Γ w) - inner ℝ w xhat ≤ γ := by sorry

end WorstCaseVaR.Entropy
