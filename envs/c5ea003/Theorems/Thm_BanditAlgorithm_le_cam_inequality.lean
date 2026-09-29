-- Prove2me | Theorems.Thm_BanditAlgorithm_le_cam_inequality
-- name    : BanditAlgorithm.le_cam_inequality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-18T23:57:26.896407+00:00
-- url     : https://prove2.me/theorems/632b65d5-39b8-477b-875b-830ef87eefd7
-- statement:
--   (Le Cam) For probability measures $P, Q$ on $(\Omega,\mathcal{F})$ with $D(P,Q) = $ `klDiv P Q` finite:
--
--   $$\int (p \wedge q)\, d\nu \ge \frac{1}{2}\exp(-D(P,Q)),$$
--
--   where $\nu = P+Q$ is the canonical common dominating measure and $p = dP/d\nu$, $q = dQ/d\nu$ are Radon-Nikodym derivatives (Mathlib `Measure.rnDeriv`), stated as a lower bound on the lintegral of their pointwise min. This chains the book's two steps
--
--   $$\int p\wedge q \ge \frac12\Big(\int\sqrt{pq}\Big)^2 \ge \frac12 e^{-D}$$
--
--   into the reusable testing-affinity bound. The hypothesis $D(P,Q) \ne \infty$ is REQUIRED by the Lean encoding: `(klDiv P Q).toReal` is the junk value $0$ at $\infty$, making the right-hand side $\frac12$, while for mutually singular $P \perp Q$ the left-hand side is $0$. (The book's statement is trivially true at $D=\infty$ since $e^{-\infty}=0$.)
-- source:
--   L&S proof of Theorem 14.2, pp.190-191

import Mathlib.InformationTheory.KullbackLeibler.Basic


open MeasureTheory InformationTheory
open scoped ENNReal

theorem BanditAlgorithm.le_cam_inequality {Ω : Type} {mΩ : MeasurableSpace Ω}
    (P Q : Measure Ω) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (hD : klDiv P Q ≠ ∞) :
    ENNReal.ofReal (2⁻¹ * Real.exp (-(klDiv P Q).toReal)) ≤
      ∫⁻ ω, min (P.rnDeriv (P + Q) ω) (Q.rnDeriv (P + Q) ω) ∂(P + Q) := by
  sorry
