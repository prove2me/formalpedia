-- Prove2me | Theorems.Thm_MetricGeometry_eVariationOn_eq_of_localChordLaw
-- name    : MetricGeometry.eVariationOn_eq_of_localChordLaw
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T23:31:09.89037+00:00
-- url     : https://prove2.me/theorems/8d4b619e-519c-408b-ae2a-b322dcb6994f
-- title:
--   A curve obeying a local circular chord law has length $kL(b-a)$
-- statement:
--   Let $c:\mathbb R\to X$ be a curve in a metric space obeying, on every pair of parameters at distance at most $\delta>0$, the chord law of a circle of radius $L\ge0$ traversed at angular rate $k\ge0$:
--
--   $$
--   d\bigl(c(s),c(t)\bigr)=2L\left|\sin\frac{k(s-t)}{2}\right|\qquad\text{whenever }|s-t|\le\delta .
--   $$
--
--   Then for $a\le b$ the length of $c$ over $[a,b]$ — its total variation — is
--
--   $$
--   \operatorname{Length}\bigl(c|_{[a,b]}\bigr)=k\,L\,(b-a).
--   $$
--
--   **Role.** A curve satisfying this hypothesis is locally isometric to an arc of a Euclidean circle, and the theorem says that its length is the arclength of the corresponding arc. It is the precise form of the passage from chord to arc: the distance between two points of the curve is *strictly smaller* than $kL|s-t|$ whenever they are distinct, and the missing amount is recovered only in the limit over ever finer subdivisions.
--
--   The two halves of the proof use the hypothesis in opposite directions. Since $|\sin x|\le|x|$, the chord law makes $c$ locally, and hence — by chaining along steps of size $\delta$ — globally $kL$-Lipschitz, which bounds every partition sum by a telescoping argument. Conversely the uniform partition of $[a,b]$ into $n$ pieces of mesh at most $\delta$ has chord sum exactly $2Ln\lvert\sin\frac{k(b-a)}{2n}\rvert$, and these converge to $kL(b-a)$ as $n\to\infty$ because $\sin x/x\to1$. The supremum defining the variation therefore has the stated value.
--
--   This computes the length of the circle in the image of a homogeneous harmonic map into a conical Euclidean building whose unit circle lies at constant distance $L$ from the cone point: on each small arc the image lies in a single apartment as a circular arc of radius $L$ traversed at rate $\alpha$, so the length over a full turn is $2\pi\alpha L$.
-- source:
--   Standard metric geometry; the computation is the one behind Lemma 3.2 of C. Breiner and B. K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calc. Var. PDE (2026), arXiv:2604.16608. Mathlib has `eVariationOn` but no computation of the length of a curve from a local chord law.

import Definitions.Def_metric_npc_cone

namespace MetricGeometry

theorem eVariationOn_eq_of_localChordLaw {X : Type*} [PseudoMetricSpace X]
    (c : ℝ → X) (k L delta : ℝ)
    (hk : 0 ≤ k) (hL : 0 ≤ L) (hd : 0 < delta)
    (hchord : ∀ s t : ℝ, |s - t| ≤ delta →
      dist (c s) (c t) = 2 * L * |Real.sin (k * (s - t) / 2)|)
    (a b : ℝ) (hab : a ≤ b) :
    eVariationOn c (Set.Icc a b) = ENNReal.ofReal (k * L * (b - a)) := by sorry

end MetricGeometry
