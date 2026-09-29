-- Prove2me | Theorems.Thm_HarmonicBuilding_constantSpeedLocalGeodesicVariation
-- name    : HarmonicBuilding.constantSpeedLocalGeodesicVariation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-27T15:05:03.936952+00:00
-- url     : https://prove2.me/theorems/2588e4ab-fa68-48a9-99b4-843703056218
-- title:
--   A local geodesic of speed $k$ has variation $k(b-a)$
-- statement:
--   Let $X$ be a metric space and let $c:\mathbb{R}\to X$ be a curve that is a *local geodesic of constant speed* $k\ge0$: there is $\delta>0$ with
--
--   $$
--   d\bigl(c(s),c(t)\bigr)=k\,|s-t| \qquad\text{whenever }|s-t|\le\delta .
--   $$
--
--   Then on every interval the total variation of $c$ is speed times elapsed parameter:
--
--   $$
--   \operatorname{Var}_{[a,b]}(c) \;=\; k\,(b-a) \qquad (a\le b).
--   $$
--
--   The hypothesis is genuinely local and cannot be strengthened without losing the intended applications: a closed curve, such as a circle traversed once, satisfies it while failing the corresponding global identity, since its endpoints coincide.
--
--   Two observations drive the proof. On an interval of length at most $\delta$ every partition sum telescopes exactly, because each consecutive pair is within $\delta$, so the variation there is exactly $k$ times the length; the reverse inequality comes from the two-point partition. For a general interval one chops $[a,b]$ into finitely many pieces of length $\delta$ and adds, using additivity of the variation across a common endpoint.
--
--   The statement is a general fact about metric spaces with no analysis in it, and it is what converts a local speed computation into a length. In the setting of harmonic maps into buildings it is applied to the image of the unit circle, whose local speed is $\alpha L$, to produce the length $2\pi\alpha L$.
--
--   **Formalization Note.** The variation is Mathlib's `eVariationOn`, the supremum of $\sum d(c(u_{i+1}),c(u_i))$ over finite increasing sequences, valued in the extended nonnegative reals; the right-hand side is therefore the coercion of $k(b-a)$.
-- source:
--   Elementary metric-space fact underlying the length computations of Christine Breiner and Ben K. Dees, On the Possible Orders of Harmonic Maps into Euclidean Buildings, Calculus of Variations and Partial Differential Equations (2026), arXiv:2604.16608, https://doi.org/10.1007/s00526-026-03375-5, specifically the passage from constant speed to length in Lemma 3.2 (Section 3) and Lemma 4.2 (2) (Section 4). Stated here in general form, with no reference to buildings or harmonic maps.

import Mathlib

namespace HarmonicBuilding

theorem constantSpeedLocalGeodesicVariation {X : Type*} [PseudoMetricSpace X]
    (c : ℝ → X) (k delta : ℝ) (hk : 0 ≤ k) (hdelta : 0 < delta)
    (hloc : ∀ s t : ℝ, |s - t| ≤ delta → dist (c s) (c t) = k * |s - t|)
    (a b : ℝ) (hab : a ≤ b) :
    eVariationOn c (Set.Icc a b) = ENNReal.ofReal (k * (b - a)) := by sorry

end HarmonicBuilding
