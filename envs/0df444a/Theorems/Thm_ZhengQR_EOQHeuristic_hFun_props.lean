-- Prove2me | Theorems.Thm_ZhengQR_EOQHeuristic_hFun_props
-- name    : ZhengQR.EOQHeuristic.hFun_props
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T01:43:06.98678+00:00
-- url     : https://prove2.me/theorems/0cda06ef-df3d-473d-b534-37415a222c52
-- title:
--   Lemma 4 — $H$ is increasing and convex on $[0,\infty)$ with asymptotic slope $hp/(h + p)$
-- statement:
--   In the stochastic $(Q, r)$ model (as in Lemma 2, with $K > 0$), let $H(Q) = G(r(Q))$ for $Q > 0$ and $H(0) = G(y^0)$. Then
--
--   1. $H$ is strictly increasing on $[0, \infty)$;
--   2. $H$ is convex on $[0, \infty)$;
--   3. $H$ is right-continuous at $0$, i.e. $\lim_{Q \to 0^+} G(r(Q)) = G(y^0)$;
--   4. every chord of $H$ on $[0,\infty)$ has slope at most $hp/(h+p)$: for $0 \le Q < Q'$,
--   $$H(Q') - H(Q) \le \frac{hp}{h+p}\,(Q' - Q);$$
--   5. $$\lim_{Q \to \infty} \frac{H(Q)}{Q} = \frac{hp}{h+p}.$$
--
--   The paper states: "$H(Q)$ is an increasing convex function with asymptotic slope $hp/(h+p)$ as $Q \uparrow \infty$". The slope $hp/(h+p)$ is exactly the slope of the EOQ model's counterpart $H_d$, which makes this lemma the basis of every comparison between the two models.
--
--   **Formalization Note** "Increasing" is read as strictly increasing (the proof shows $H' > 0$). "Asymptotic slope $hp/(h+p)$" is read as items 4 and 5: the proof shows $H'(Q) \uparrow hp/(h+p)$, and later proofs use it as the bound $H'(Q) \le hp/(h+p)$; for a convex $H$ without assumed differentiability, the chord bound plus the limit of $H(Q)/Q$ express exactly this. Item 3 is the content of the paper's "$H(0) \stackrel{\text{def}}{=} \lim_{Q\to0+} G(r(Q)) = G(y^0)$" (p. 91), since here $H(0)$ is defined as $G(y^0)$.
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 91, Lemma 4 (and the definition of H(0) under Eq. (6))

import Mathlib
import Definitions.Def_ZhengQR_EOQHeuristic_qrCost
import Definitions.Def_ZhengQR_EOQHeuristic_costCurves
import Definitions.Def_ZhengQR_EOQHeuristic_stochasticModel
open MeasureTheory Filter Topology

namespace ZhengQR.EOQHeuristic

theorem hFun_props {lam L K h p : ℝ} {μ : Measure ℝ} (hM : IsQRModel lam L h p μ) (hK : 0 < K) :
    StrictMonoOn (hFun (newsvendorCost μ h p) lam K) (Set.Ici 0) ∧
    ConvexOn ℝ (Set.Ici 0) (hFun (newsvendorCost μ h p) lam K) ∧
    ContinuousWithinAt (hFun (newsvendorCost μ h p) lam K) (Set.Ici 0) 0 ∧
    (∀ Q Q' : ℝ, 0 ≤ Q → Q < Q' → hFun (newsvendorCost μ h p) lam K Q' - hFun (newsvendorCost μ h p) lam K Q ≤ h * p / (h + p) * (Q' - Q)) ∧
    Tendsto (fun Q : ℝ => hFun (newsvendorCost μ h p) lam K Q / Q) atTop (𝓝 (h * p / (h + p))) := by sorry

end ZhengQR.EOQHeuristic
