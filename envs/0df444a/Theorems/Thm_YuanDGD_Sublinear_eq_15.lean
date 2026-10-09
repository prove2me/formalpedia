-- Prove2me | Theorems.Thm_YuanDGD_Sublinear_eq_15
-- name    : YuanDGD.Sublinear.eq_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T09:20:22.587187+00:00
-- url     : https://prove2.me/theorems/d621a097-3822-4bdc-ba02-588baa24c54a
-- title:
--   (15), p. 10 — the mean iterate follows x̄(k + 1) = x̄(k) − αg(k)
-- statement:
--   Let $W$ be doubly stochastic. For any stepsize $\alpha$ and any functions $f_i$, the mean of the DGD iterates (4) satisfies, for every $k \ge 0$,
--   $$\bar x(k+1) = \bar x(k) - \alpha\, g(k), \qquad g(k) = \frac1n\sum_{i=1}^n \nabla f_i(x_{(i)}(k)).$$
--
--   Averaging the iteration removes the mixing step, so the mean moves as gradient descent on $\bar f$ with the inexact gradient $g(k)$ in place of $\bar g(k) = \nabla\bar f(\bar x(k))$.
--
--   **Formalization Note.** Only the unit column sums of $W$ are needed; no other hypothesis is assumed.
-- source:
--   Yuan, Ling & Yin, On the Convergence of Decentralized Gradient Descent, arXiv:1310.7063v3, p. 10, (15)

import Mathlib
import Definitions.Def_YuanDGD_Sublinear_Setting

namespace YuanDGD.Sublinear

open YuanDGD.Linear

/-- Yuan–Ling–Yin, arXiv:1310.7063v3, (15), p. 10: if `W` is doubly stochastic, the mean of the DGD
iterates (4) follows `x̄(k + 1) = x̄(k) − αg(k)`. -/
theorem eq_15 {n p : ℕ} (W : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → E p → ℝ)
    (hds : W ∈ doublyStochastic ℝ (Fin n)) (α : ℝ) :
    ∀ k : ℕ, xbar (dgd W f α) (k + 1) = xbar (dgd W f α) k - α • gk f (dgd W f α) k := by sorry

end YuanDGD.Sublinear
