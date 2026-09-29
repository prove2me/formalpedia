-- Prove2me | Theorems.Thm_WorstCaseVaR_Entropy_worst_case_probability_dual
-- name    : WorstCaseVaR.Entropy.worst_case_probability_dual
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T14:19:33.088093+00:00
-- url     : https://prove2.me/theorems/359a2892-b714-485d-b400-3fc494ee4fd7
-- title:
--   p. 554 — the worst-case probability is the infimum of the dual over λ > 0
-- statement:
--   Let $P_0 = \mathcal N(\hat x, \Gamma)$ with $\Gamma \succ 0$, let $w \in \mathbb R^n$ be nonzero, $d \ge 0$ and $\gamma \in \mathbb R$. Write $\mathcal S_\gamma = \{x : \gamma \le -x^\top w\}$, $\phi(\gamma) = P_0(\mathcal S_\gamma)$, and $\mathcal P_d$ for the probability distributions $P$ on $\mathbb R^n$ with $\mathrm{KL}(P,P_0) \le d$. Then the worst-case probability equals the dual value:
--   $$\sup_{P \in \mathcal P_d} P(\mathcal S_\gamma) \;=\; \inf_{\lambda > 0} \Big(\lambda d + \lambda \log\big((e^{1/\lambda} - 1)\phi(\gamma) + 1\big)\Big).$$
--
--   This is the strong-duality step of the proof of Theorem 9 (the paper cites Smith 1995 for it); it reduces the infinite-dimensional worst case over distributions to a scalar minimisation.
--
--   **Formalization Note** Both sides are encoded without Lean's `sSup`/`sInf`: the statement asserts a real number $\theta$ that is the least upper bound of $\{P(\mathcal S_\gamma) : P \in \mathcal P_d\}$ and the greatest lower bound of the dual values over $\lambda > 0$. Probabilities are real-valued (`measureReal`).
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 554, proof of Theorem 9, sentence after Eq. (48)

import Mathlib
import Definitions.Def_WorstCaseVaR_Entropy_Basic

namespace WorstCaseVaR.Entropy

/-- p. 554: the worst-case probability `sup_{P : KL(P, P₀) ≤ d} P{γ ≤ -xᵀw}` equals the
infimum over `λ > 0` of `λd + λ log((e^{1/λ} - 1)φ(γ) + 1)`, where `φ(γ) = P₀{γ ≤ -xᵀw}`. -/
theorem worst_case_probability_dual {n : ℕ} (xhat w : Returns n) (Γ : Matrix (Fin n) (Fin n) ℝ)
    (hΓ : Γ.PosDef) (hw : w ≠ 0) (d : ℝ) (hd : 0 ≤ d) (γ : ℝ) :
    ∃ θ : ℝ,
      IsLUB {p | ∃ P ∈ klBall xhat Γ d, P.real (lossSet w γ) = p} θ ∧
      IsGLB (dualValue d ((refGaussian xhat Γ).real (lossSet w γ)) '' Set.Ioi 0) θ := by sorry

end WorstCaseVaR.Entropy
