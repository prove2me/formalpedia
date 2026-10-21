-- Prove2me | Theorems.Thm_WrightPDIPM_Infeasible_theorem_6_9
-- name    : WrightPDIPM.Infeasible.theorem_6_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:54:03.257133+00:00
-- url     : https://prove2.me/theorems/c29d8e46-078e-42d4-85a2-04e294df3979
-- title:
--   Theorem 6.9 — if F° ≠ ∅ the iterates (x^k, s^k) of Algorithm IPF are bounded and have a limit point
-- statement:
--   Let $(x^k,\lambda^k,s^k)$ be the iterates of Algorithm IPF for data $A \in \mathbb{R}^{m\times n}$, $b$, $c$, with parameters $\gamma \in (0,1)$, $\beta \ge 1$, $0 < \sigma_{\min} < \sigma_{\max} \le 0.5$. Assume $n \ge 1$, $(r_b^0,r_c^0) \ne 0$, and that the set of strictly feasible points
--
--   $$\mathcal F^\circ = \{(x,\lambda,s) : Ax = b,\ A^{\mathsf T}\lambda + s = c,\ (x,s) > 0\}$$
--
--   is nonempty. Then the sequence $\{(x^k,s^k)\}$ is bounded, and therefore has at least one limit point.
--
--   Without strict feasibility the algorithm is still defined, but the iterates may be unbounded; this theorem is what guarantees that the limit points described in Theorem 6.8 exist.
--
--   **Formalization Note** Boundedness is stated as a uniform bound $|x^k_i| \le M$, $|s^k_i| \le M$ for all $k$ and $i$; a limit point is a cluster point of $k \mapsto (x^k,s^k)$ in $\mathbb{R}^n\times\mathbb{R}^n$. $(r_b^0,r_c^0) \ne 0$ (p. 111) and $n \ge 1$ are explicit; $\mathcal F^\circ \ne \emptyset$ is the theorem's own hypothesis.
-- source:
--   Wright, Primal-Dual Interior-Point Methods, SIAM 1997, p. 123, Theorem 6.9 (proof pp. 123–124); F° from (1.7b), p. 5; (r_b⁰, r_c⁰) ≠ 0 from p. 111

import Mathlib
import Definitions.Def_WrightPDIPM_Infeasible_IPF

namespace WrightPDIPM.Infeasible

open Filter

/-- Theorem 6.9 (p. 123): along Algorithm IPF with an infeasible start, if `F° ≠ ∅` then the
sequence `{(xᵏ, sᵏ)}` is bounded and therefore has at least one limit point. -/
theorem theorem_6_9 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (γ β σmin σmax : ℝ) (hγ : 0 < γ ∧ γ < 1) (hβ : 1 ≤ β)
    (hσ : 0 < σmin ∧ σmin < σmax ∧ σmax ≤ 0.5)
    (hn : 0 < n)
    (x : ℕ → Fin n → ℝ) (lam : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ) (σ α : ℕ → ℝ)
    (dx : ℕ → Fin n → ℝ) (dlam : ℕ → Fin m → ℝ) (ds : ℕ → Fin n → ℝ)
    (hrun : IsIPFIterates A b c γ β σmin σmax x lam s σ α dx dlam ds)
    (hinf : (rb A b (x 0), rc A c (lam 0) (s 0)) ≠ (0, 0))
    (hFo : (Fo A b c).Nonempty) :
    (∃ M : ℝ, ∀ k i, |x k i| ≤ M ∧ |s k i| ≤ M) ∧
    ∃ q : (Fin n → ℝ) × (Fin n → ℝ), MapClusterPt q atTop (fun k => (x k, s k)) := by sorry

end WrightPDIPM.Infeasible
