-- Prove2me | Theorems.Thm_ZhengQR_CostBounds_area_chain
-- name    : ZhengQR.CostBounds.area_chain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T02:01:18.142234+00:00
-- url     : https://prove2.me/theorems/cdc2870e-2a33-44c2-84c8-f29faa69db76
-- title:
--   Lemma 8: $\int_0^Q H \ge \frac12 QH(Q) \ge A(Q) \ge \frac12 QH_0(Q) \ge \int_0^Q H_0$, with equality for deterministic demand
-- statement:
--   In the stochastic $(Q,r)$ model, for every $Q\ge0$,
--   $$\int_0^Q H(y)\,dy\;\ge\;\tfrac12 QH(Q)\;\ge\;A(Q)\;\ge\;\tfrac12 QH_0(Q)\;\ge\;\int_0^Q H_0(y)\,dy,$$
--   and all four inequalities hold as equalities when the leadtime demand is deterministic, i.e. when $D=\lambda L$ almost surely.
--
--   The chain compares the area $A(Q)$ between the chord and the $G$-curve with the triangle areas $\tfrac12QH(Q)$ and $\tfrac12QH_0(Q)$; it is used in the proofs of Theorems 2, 3 and 5.
--
--   **Formalization Note** The paper states the chain without a domain; its proof works on $[0,Q]$, so $Q\ge0$ is taken. "Deterministic" is encoded as $\mu$ equal to the Dirac mass at $\lambda L$ (the model's mean forces the point).
-- source:
--   Zheng, On Properties of Stochastic Inventory Systems, Management Science 38(1), 1992, p. 95, Lemma 8

import Mathlib
import Definitions.Def_ZhengQR_CostBounds_QRMachinery
import Definitions.Def_ZhengQR_CostBounds_Model

namespace ZhengQR.CostBounds

open MeasureTheory

theorem area_chain (M : QRModel) :
    (∀ Q : ℝ, 0 ≤ Q →
      1 / 2 * Q * Hfun M.G M.lam M.K Q ≤ ∫ y in (0 : ℝ)..Q, Hfun M.G M.lam M.K y ∧
      Afun M.G M.lam M.K Q ≤ 1 / 2 * Q * Hfun M.G M.lam M.K Q ∧
      1 / 2 * Q * H0fun M.G M.lam M.K Q ≤ Afun M.G M.lam M.K Q ∧
      ∫ y in (0 : ℝ)..Q, H0fun M.G M.lam M.K y ≤ 1 / 2 * Q * H0fun M.G M.lam M.K Q) ∧
    (M.μ = Measure.dirac (M.lam * M.L) → ∀ Q : ℝ, 0 ≤ Q →
      1 / 2 * Q * Hfun M.G M.lam M.K Q = ∫ y in (0 : ℝ)..Q, Hfun M.G M.lam M.K y ∧
      Afun M.G M.lam M.K Q = 1 / 2 * Q * Hfun M.G M.lam M.K Q ∧
      1 / 2 * Q * H0fun M.G M.lam M.K Q = Afun M.G M.lam M.K Q ∧
      ∫ y in (0 : ℝ)..Q, H0fun M.G M.lam M.K y = 1 / 2 * Q * H0fun M.G M.lam M.K Q) := by sorry

end ZhengQR.CostBounds
