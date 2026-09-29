-- Prove2me | Theorems.Thm_MetricGeometry_limsup_comparisonAngle_le_alexandrovAngle
-- name    : MetricGeometry.limsup_comparisonAngle_le_alexandrovAngle
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T01:18:28.989761+00:00
-- url     : https://prove2.me/theorems/bf5ba569-1258-49e3-ae6b-3cd0eca3fbaa
-- title:
--   Freezing one parameter does not increase the upper angle
-- statement:
--   Let $X$ be a metric space, let $c$ be a curve issuing from $p$ and parametrised by arclength on $(0,a]$, and let
--   $c'$ be a geodesic issuing from $p$ and parametrised by arclength on $[0,b]$. Then for every fixed
--   $t\in(0,b]$ the second parameter may be frozen without increasing the angle:
--
--   $$\limsup_{s\to 0^+}\ \widetilde\angle_p\bigl(c(s),c'(t)\bigr)\ \le\ \angle(c,c'),$$
--
--   where $\angle(c,c')=\limsup_{s,r\to0^+}\widetilde\angle_p(c(s),c'(r))$ is the Alexandrov angle.
--
--   **Role.** Alexandrov gave a second description of the angle between two geodesics, the *strong upper angle*
--
--   $$\gamma(c,c')=\limsup_{s\to 0^+,\ r\in(0,b]}\widetilde\angle_p\bigl(c(s),c'(r)\bigr),$$
--
--   in which only one of the two parameters is required to tend to $0$. That $\gamma(c,c')\ge\angle(c,c')$ is
--   immediate from the definitions; the statement above is exactly the reverse inequality, applied at each fixed
--   $t$, and it is the whole content of the identification $\angle(c,c')=\gamma(c,c')$. Having the two descriptions
--   agree is what makes the angle usable in situations where one of the two geodesics is held fixed — for instance
--   when comparing a geodesic with a fixed point of the space rather than with a second germ at $p$.
--
--   **The argument.** The engine is the two-sided estimate
--
--   $$\frac{r-d(c(s),c'(r))}{s}\ \le\ \cos\widetilde\angle_p(c(s),c'(r))\ \le\ \frac{r-d(c(s),c'(r))}{s}+\frac{s}{2r}.$$
--
--   Because $c'$ is a geodesic, $d(c'(r),c'(t))=t-r$ for $0<r\le t$, and the triangle inequality gives
--   $r-d(c(s),c'(r))\le t-d(c(s),c'(t))$. Feeding this between the upper estimate at $r$ and the lower estimate at
--   $t$ yields the key comparison
--
--   $$\cos\widetilde\angle_p\bigl(c(s),c'(r)\bigr)\ \le\ \cos\widetilde\angle_p\bigl(c(s),c'(t)\bigr)+\frac{s}{2r},
--   \qquad 0<r\le t .$$
--
--   Now fix $\eta>0$; one may assume $\angle(c,c')+\eta<\pi$, for otherwise the bound is trivial. Put
--   $\delta=\eta/2$. By definition of the $\limsup$ over the product filter there is $\varepsilon>0$ with
--   $\widetilde\angle_p(c(s),c'(r))<\angle(c,c')+\delta$ whenever $s,r<\varepsilon$. Choose one such $r$ with
--   $r\le t$ and hold it fixed. Since cosine is decreasing on $[0,\pi]$ this gives
--   $\cos\widetilde\angle_p(c(s),c'(r))\ge\cos(\angle(c,c')+\delta)$, so by the key comparison
--
--   $$\cos\widetilde\angle_p\bigl(c(s),c'(t)\bigr)\ \ge\ \cos\bigl(\angle(c,c')+\delta\bigr)-\frac{s}{2r}.$$
--
--   The number $\kappa=\cos(\angle(c,c')+\delta)-\cos(\angle(c,c')+2\delta)$ is strictly positive because cosine is
--   strictly decreasing on $[0,\pi]$ and $\angle(c,c')+2\delta\le\pi$. Hence for all sufficiently small $s$ the
--   right-hand side exceeds $\cos(\angle(c,c')+2\delta)$, and monotonicity of cosine turns that back into
--   $\widetilde\angle_p(c(s),c'(t))<\angle(c,c')+2\delta=\angle(c,c')+\eta$. Taking the $\limsup$ in $s$ and letting
--   $\eta\to0$ finishes the proof.
--
--   **Formalization Note.** The curve $c$ is only assumed to satisfy $d(p,c(s))=s$ on $(0,a]$, which is all the
--   argument uses; $c'$ is assumed to be a genuine arclength geodesic on $[0,b]$, since the proof needs
--   $d(c'(r),c'(t))=|r-t|$.
-- source:
--   The content of Proposition I.1.16 (the strong upper angle of Alexandrov [Ale51], [Ale57a] agrees with the Alexandrov angle of Definition I.1.12) in M. Bridson and A. Haefliger, Metric Spaces of Non-Positive Curvature, Springer Grundlehren der mathematischen Wissenschaften 319, Chapter I.1 (Angles); its proof reduces to showing that for each fixed t one has limsup_{s->0} of the comparison angle at most the Alexandrov angle, which is the statement formalised here, and rests on the technical estimate Lemma I.1.17.

import Definitions.Def_metric_alexandrov_angle

namespace MetricGeometry

open Filter Topology

theorem limsup_comparisonAngle_le_alexandrovAngle {X : Type*} [PseudoMetricSpace X]
    (p : X) (c c' : ℝ → X) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hc : ∀ s ∈ Set.Ioc (0:ℝ) a, dist p (c s) = s)
    (hc'0 : c' 0 = p)
    (hc' : ∀ r ∈ Set.Icc (0:ℝ) b, ∀ r' ∈ Set.Icc (0:ℝ) b,
      dist (c' r) (c' r') = |r - r'|)
    (t : ℝ) (ht : 0 < t) (htb : t ≤ b) :
    Filter.limsup (fun s : ℝ => comparisonAngle p (c s) (c' t)) (𝓝[>] (0:ℝ))
      ≤ alexandrovAngle p c c' := by sorry

end MetricGeometry
