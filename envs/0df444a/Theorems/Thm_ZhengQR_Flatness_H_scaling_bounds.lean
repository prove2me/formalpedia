-- Prove2me | Theorems.Thm_ZhengQR_Flatness_H_scaling_bounds
-- name    : ZhengQR.Flatness.H_scaling_bounds
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T02:08:11.340616+00:00
-- url     : https://prove2.me/theorems/b5f97650-6f92-4f67-9821-3865a2486015
-- title:
--   Eqs. (26)–(27): H(αQ) ≤ αH(Q) for α > 1 and H(αQ) ≥ αH(Q) for 0 < α < 1
-- statement:
--   In the stochastic $(Q, r)$ model, let $H(Q) = G(r(Q))$. For every $Q>0$,
--
--   $$H(\alpha Q) \le \alpha H(Q) \quad \forall \alpha>1, \qquad H(\alpha Q) \ge \alpha H(Q) \quad \forall\, 0<\alpha<1.$$
--
--   Equivalently, $H(Q')/Q'$ is at least $H(Q)/Q$ below $Q$ and at most $H(Q)/Q$ above it along the ray through $Q$. These two inequalities are the pointwise estimates behind Lemma 9.
--
--   **Formalization Note** The paper derives (26) and (27) inside the proof of Lemma 9 for fixed $Q>0$; they are stated here with the same quantifiers.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 98, Eqs. (26)–(27) (proof of Lemma 9)

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

theorem H_scaling_bounds (M : QRModel) (Q : ℝ) (hQ : 0 < Q) :
    (∀ α : ℝ, 1 < α → M.H (α * Q) ≤ α * M.H Q) ∧
      (∀ α : ℝ, 0 < α → α < 1 → α * M.H Q ≤ M.H (α * Q)) := by sorry

end ZhengQR.Flatness
