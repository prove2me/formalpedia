-- Prove2me | Theorems.Thm_WorstCaseVaR_KnownMoments_worst_case_var_equivalences
-- name    : WorstCaseVaR.KnownMoments.worst_case_var_equivalences
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:16:30.643795+00:00
-- url     : https://prove2.me/theorems/32b72d98-602c-41ec-b7bf-28cdf624c5af
-- title:
--   Theorem 1 — five equivalent representations of the worst-case VaR under known mean and covariance
-- statement:
--   Let $\hat x \in \mathbb R^n$ and let $\Gamma$ be a positive definite $n\times n$ matrix. Let $\mathcal P$ be the set of all probability distributions on $\mathbb R^n$ with mean $\hat x$ and covariance matrix $\Gamma$. Fix a portfolio $w \in \mathbb R^n$ with $w \ne 0$, a loss probability level $\varepsilon \in (0,1)$ and a loss level $\gamma \in \mathbb R$. Let $\kappa(\varepsilon) = \sqrt{(1-\varepsilon)/\varepsilon}$, let $\Sigma = \begin{bmatrix} \Gamma + \hat x\hat x^\top & \hat x \\ \hat x^\top & 1\end{bmatrix}$ be the second-moment matrix, and write $\langle A, B\rangle = \operatorname{Tr}(AB)$. The following propositions are equivalent.
--
--   1. The worst-case VaR at level $\varepsilon$ is at most $\gamma$:
--   $$\sup_{P \in \mathcal P} \operatorname{Prob}_P\{\gamma \le -w^\top x\} \le \varepsilon.$$
--   2. $$\kappa(\varepsilon)\,\|\Gamma^{1/2}w\|_2 - \hat x^\top w \le \gamma.$$
--   3. There exist a symmetric $(n+1)\times(n+1)$ matrix $M$ and $\tau \in \mathbb R$ with
--   $$\langle M, \Sigma\rangle \le \tau\varepsilon,\quad M \succeq 0,\quad \tau \ge 0,\quad M + \begin{bmatrix} 0 & w \\ w^\top & -\tau + 2\gamma\end{bmatrix} \succeq 0.$$
--   4. For every $x \in \mathbb R^n$ with $\begin{bmatrix}\Gamma & x - \hat x\\ (x - \hat x)^\top & \kappa(\varepsilon)^2\end{bmatrix} \succeq 0$ we have $-x^\top w \le \gamma$.
--   5. There exist a symmetric $n\times n$ matrix $\Lambda$ and $v \in \mathbb R$ with
--   $$\langle \Lambda, \Gamma\rangle + \kappa(\varepsilon)^2 v - \hat x^\top w \le \gamma, \qquad \begin{bmatrix}\Lambda & w/2\\ w^\top/2 & v\end{bmatrix} \succeq 0.$$
--
--   Proposition 2 is a closed form of the worst-case Value-at-Risk $V_{\mathcal P}(w)$: it is the smallest $\gamma$ satisfying 1, namely $\kappa(\varepsilon)\|\Gamma^{1/2}w\|_2 - \hat x^\top w$. Propositions 3–5 are semidefinite representations that extend to the case where the moments are only known to lie in a set.
--
--   **Formalization Note.**
--   1. The supremum in Proposition 1 is encoded as "every $P \in \mathcal P$ has $P(\mathcal S) \le \varepsilon$", with the probability in $[0,\infty]$ compared with $\varepsilon$.
--   2. The paper prints $\varepsilon \in (0,1]$. At $\varepsilon = 1$ Proposition 1 holds for every $\gamma$, while Propositions 2–5 reduce to $\gamma \ge -\hat x^\top w$, so the theorem is stated for $0 < \varepsilon < 1$.
--   3. The hypothesis $w \ne 0$ is the paper's standing assumption that the admissible set of portfolios does not contain $0$ (used in its proof); with $w = 0$ and $\gamma = 0$, Proposition 1 fails and Proposition 2 holds.
--   4. "Less than $\gamma$" is the non-strict inequality of the display.
--   5. $\|\Gamma^{1/2}w\|_2$ is written $\sqrt{w^\top\Gamma w}$. The class $\mathcal P$ is `HasMeanCov` (any Borel probability measure with these first two moments, square-integrable coordinates).
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), pp. 545–546, Theorem 1, Eqs. (7)–(11); worst-case VaR Eq. (4), p. 544; w ≠ 0 from p. 543

import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

/-- **Theorem 1** (El Ghaoui–Oks–Oustry 2003, pp. 545–546). Let `𝒫` be the set of probability
distributions on `ℝⁿ` with mean `x̂` and covariance matrix `Γ ≻ 0`, let `w ≠ 0`,
`ε ∈ (0, 1)` and `γ ∈ ℝ`. The following are equivalent:
1. `sup_{P ∈ 𝒫} Prob{γ ≤ -wᵀx} ≤ ε`;
2. `κ(ε) ‖Γ^{1/2} w‖₂ - x̂ᵀw ≤ γ` (7);
3. there exist `M ∈ 𝒮_{n+1}`, `τ ∈ ℝ` with `⟨M, Σ⟩ ≤ τε`, `M ⪰ 0`, `τ ≥ 0`,
   `M + [[0, w], [wᵀ, -τ + 2γ]] ⪰ 0` (9);
4. for every `x` with `[[Γ, x - x̂], [(x - x̂)ᵀ, κ(ε)²]] ⪰ 0` (10), `-xᵀw ≤ γ`;
5. there exist `Λ ∈ 𝒮_n`, `v ∈ ℝ` with `⟨Λ, Γ⟩ + κ(ε)² v - x̂ᵀw ≤ γ` and
   `[[Λ, w/2], [wᵀ/2, v]] ⪰ 0` (11).
The printed range `ε ∈ (0, 1]` is read as `(0, 1)`: at `ε = 1` item 1 holds for every `γ`. -/
theorem worst_case_var_equivalences {n : ℕ}
    (xhat w : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (hw : w ≠ 0) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (γ : ℝ) :
    List.TFAE
      [ ∀ P : Measure (EuclideanSpace ℝ (Fin n)), HasMeanCov P xhat Γ →
          P (lossSet w γ) ≤ ENNReal.ofReal ε,
        kappa ε * Real.sqrt (⇑w ⬝ᵥ Γ *ᵥ ⇑w) - ⟪xhat, w⟫_ℝ ≤ γ,
        ∃ (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (τ : ℝ),
          (M * secondMomentMatrix xhat Γ).trace ≤ τ * ε ∧ M.PosSemidef ∧ 0 ≤ τ ∧
          (M + bordered 0 ⇑w (-τ + 2 * γ)).PosSemidef,
        ∀ x : EuclideanSpace ℝ (Fin n),
          (bordered Γ ⇑(x - xhat) (kappa ε ^ 2)).PosSemidef → -⟪x, w⟫_ℝ ≤ γ,
        ∃ (Λ : Matrix (Fin n) (Fin n) ℝ) (v : ℝ), Λ.IsSymm ∧
          (Λ * Γ).trace + kappa ε ^ 2 * v - ⟪xhat, w⟫_ℝ ≤ γ ∧
          (bordered Λ ((1 / 2 : ℝ) • ⇑w) v).PosSemidef ] := by sorry

end WorstCaseVaR.KnownMoments
