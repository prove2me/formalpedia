-- Prove2me | Theorems.Thm_WorstCaseVaR_KnownMoments_worst_case_probability_sdp
-- name    : WorstCaseVaR.KnownMoments.worst_case_probability_sdp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T14:14:42.809986+00:00
-- url     : https://prove2.me/theorems/a695e5d2-040e-41a6-b095-03b89bac6caa
-- title:
--   §2.1, p. 547 — the worst-case probability of loss is the value of an SDP
-- statement:
--   Let $\hat x \in \mathbb R^n$, let $\Gamma$ be a positive definite $n\times n$ matrix, let $w \in \mathbb R^n$ with $w \neq 0$, and let $\gamma \in \mathbb R$. Let $\mathcal P$ be the set of all probability distributions on $\mathbb R^n$ with mean $\hat x$ and covariance matrix $\Gamma$, let $\mathcal S = \{x \mid \gamma \le -x^\top w\}$ be the loss set, and let $\Sigma$ be the second-moment matrix of Eq. (6). Then the worst-case probability of loss equals the value of a semidefinite program:
--
--   $$\sup_{P \in \mathcal P} P(\mathcal S) \;=\; \inf\Big\{ \langle M, \Sigma\rangle \;:\; \tau \ge 0,\ M \succeq 0,\ M + \begin{bmatrix} 0 & \tau w \\ \tau w^\top & -1 + 2\tau\gamma\end{bmatrix} \succeq 0 \Big\},$$
--
--   and both sides are finite real numbers. Here $\langle M, \Sigma\rangle = \operatorname{Tr}(M\Sigma)$.
--
--   This is the moment-duality step of the proof of Theorem 1: it turns a supremum over an infinite-dimensional family of distributions into a finite-dimensional convex program, and is the source of the SDP representation (Proposition 3) of the worst-case VaR.
--
--   **Formalization Note.** The supremum and the infimum are stated as `IsLUB` and `IsGLB` of the same real number $\theta$; neither is claimed to be attained. Probabilities are real numbers `P.real 𝒮`. The class $\mathcal P$ is `HasMeanCov`, which allows any Borel probability measure with these first two moments.
-- source:
--   El Ghaoui, Oks and Oustry, Worst-Case Value-at-Risk and Robust Portfolio Optimization: A Conic Programming Approach, Oper. Res. 51 (2003), p. 547, §2.1, proof of Theorem 1, first display ('Thus the worst-case probability (14) is the solution to the SDP in variables M, τ'), resting on Eq. (14), p. 546

import Mathlib
import Definitions.Def_WorstCaseVaR_KnownMoments_Basic

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace WorstCaseVaR.KnownMoments

/-- The worst-case probability as an SDP (p. 547, first display; Eq. (14), p. 546): the supremum of
`P(𝒮)` over all probability distributions `P` on `ℝⁿ` with mean `x̂` and covariance `Γ ≻ 0`
equals the infimum of `⟨M, Σ⟩` over `τ ≥ 0`, `M ⪰ 0`, `M + [[0, τw], [τwᵀ, -1 + 2τγ]] ⪰ 0`. -/
theorem worst_case_probability_sdp {n : ℕ}
    (xhat w : EuclideanSpace ℝ (Fin n)) (Γ : Matrix (Fin n) (Fin n) ℝ) (hΓ : Γ.PosDef)
    (hw : w ≠ 0) (γ : ℝ) :
    ∃ θ : ℝ,
      IsLUB {p : ℝ | ∃ P : Measure (EuclideanSpace ℝ (Fin n)),
          HasMeanCov P xhat Γ ∧ p = P.real (lossSet w γ)} θ ∧
      IsGLB {q : ℝ | ∃ (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ) (τ : ℝ),
          0 ≤ τ ∧ M.PosSemidef ∧
          (M + bordered 0 (τ • ⇑w) (-1 + 2 * τ * γ)).PosSemidef ∧
          q = (M * secondMomentMatrix xhat Γ).trace} θ := by sorry

end WorstCaseVaR.KnownMoments
