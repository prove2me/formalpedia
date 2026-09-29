-- Prove2me | Theorems.Thm_ZhengQR_Flatness_H_strictMono_convex_slope
-- name    : ZhengQR.Flatness.H_strictMono_convex_slope
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T02:05:36.118808+00:00
-- url     : https://prove2.me/theorems/ffd5c008-1542-4a48-a455-8973c7c38236
-- title:
--   Lemma 4: H(Q) is increasing and convex with asymptotic slope hp/(h + p)
-- statement:
--   In the stochastic $(Q, r)$ model with holding cost rate $h$ and backorder rate $p$, let $H(Q) = G(r(Q))$ for $Q>0$ and $H(0) = G(y^0)$. Then:
--
--   1. $H$ is strictly increasing on $[0,\infty)$;
--   2. $H$ is convex on $[0,\infty)$;
--   3. $H$ has asymptotic slope $hp/(h+p)$:
--   $$\lim_{Q\to\infty} \frac{H(Q)}{Q} = \frac{hp}{h+p};$$
--   4. every chord of $H$ on $[0,\infty)$ has slope at most $hp/(h+p)$: for $0\le Q_1\le Q_2$,
--   $$H(Q_2) - H(Q_1) \le \frac{hp}{h+p}\,(Q_2 - Q_1).$$
--
--   These shape properties of $H$ drive all comparisons with the EOQ model, whose counterpart $H_d$ is the line of slope $hp/(h+p)$.
--
--   **Formalization Note** The paper writes "increasing" and proves $H'(Q)>0$, so the reading is strict. "Asymptotic slope $hp/(h+p)$" is proved in the paper as $\lim H'(Q) = hp/(h+p)$; since no density is assumed, $H$ need not be differentiable, and the slope is stated as the limit of $H(Q)/Q$ (equivalent for convex $H$) together with part 4, the derivative-free form of $H'(Q) \le hp/(h+p)$ that the paper uses in the proofs of Lemmas 7, 8 and 9.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 91, Lemma 4

import Mathlib
import Definitions.Def_ZhengQR_Flatness_QRModel

namespace ZhengQR.Flatness

open Filter Topology in
theorem H_strictMono_convex_slope (M : QRModel) :
    StrictMonoOn M.H (Set.Ici 0) ∧ ConvexOn ℝ (Set.Ici 0) M.H ∧
      Tendsto (fun Q : ℝ => M.H Q / Q) atTop (𝓝 (M.h * M.p / (M.h + M.p))) ∧
      ∀ Q₁ Q₂ : ℝ, 0 ≤ Q₁ → Q₁ ≤ Q₂ →
        M.H Q₂ - M.H Q₁ ≤ M.h * M.p / (M.h + M.p) * (Q₂ - Q₁) := by sorry

end ZhengQR.Flatness
