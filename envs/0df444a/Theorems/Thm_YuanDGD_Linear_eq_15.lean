-- Prove2me | Theorems.Thm_YuanDGD_Linear_eq_15
-- name    : YuanDGD.Linear.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:19:30.141477+00:00
-- url     : https://prove2.me/theorems/063aaff8-38e7-4784-b0f0-cfca7197f87b
-- title:
--   (15), p. 10 — the mean of the DGD iterates satisfies x̄(k + 1) = x̄(k) − αg(k)
-- statement:
--   Let $W$ be a doubly stochastic $n\times n$ matrix, $f_1,\dots,f_n:\mathbb R^p\to\mathbb R$ arbitrary and $\alpha\in\mathbb R$. For the DGD iterates (4) started from $0$, the mean $\bar x(k)=\frac1n\sum_ix_{(i)}(k)$ satisfies, for every $k\ge0$,
--   $$
--   \bar x(k+1)=\bar x(k)-\alpha g(k),\qquad g(k)=\frac1n\sum_{i=1}^n\nabla f_i(x_{(i)}(k)).
--   $$
--
--   Averaging the iteration over the agents thus gives an inexact gradient step for $\bar f=\frac1n\sum_if_i$, with $g(k)$ in place of the exact gradient $\bar g(k)=\nabla\bar f(\bar x(k))$; Theorem 3 analyses this inexact step.
--
--   **Formalization Note** Only the unit column sums of $W$ are needed; double stochasticity is assumed as on the page. No hypothesis on the $f_i$ or on $\alpha$ is needed.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 10, (15)

import Mathlib
import Definitions.Def_YuanDGD_Linear_Setting

open scoped InnerProductSpace

namespace YuanDGD.Linear

/-- (15), p. 10: for a doubly stochastic `W`, the mean of the DGD iterates takes an inexact
gradient step, `x̄(k + 1) = x̄(k) − α g(k)`. -/
theorem eq_15 {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ)
    (hds : W ∈ doublyStochastic ℝ (Fin n)) (α : ℝ) :
    ∀ k : ℕ, xbar (dgd W f α) (k + 1) = xbar (dgd W f α) k - α • gk f (dgd W f α) k := by sorry

end YuanDGD.Linear
