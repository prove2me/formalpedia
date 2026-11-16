-- Prove2me | Theorems.Thm_ZonotopeContainment_AdaptiveSampling_Supplement_lemma_3_1
-- name    : ZonotopeContainment.AdaptiveSampling.Supplement.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:48:56.715205+00:00
-- url     : https://prove2.me/theorems/ce590d3a-578b-4346-98c5-c80279d5e909
-- title:
--   Lemma 3.1 — a zonotope in exact Lewis position lies between $B_2^d$ and $\sqrt d\,B_2^d$ and has volume at least $2^d$
-- statement:
--   Let $v_1,\dots,v_n\in\mathbb R^d$ be nonzero vectors and let
--   $$Z=\sum_{i=1}^n[-v_i,v_i]=\Big\{\sum_{i=1}^n t_iv_i:\ |t_i|\le1\Big\}$$
--   be the zonotope they generate. Suppose the generators are in exact Lewis position:
--   $$L(V)=\sum_{i=1}^n\frac{v_iv_i^\top}{\|v_i\|}=I .$$
--   Then, with $B_2^d$ the closed Euclidean unit ball and $\mathrm{Vol}$ Lebesgue measure on $\mathbb R^d$,
--   $$B_2^d\subseteq Z\subseteq\sqrt d\,B_2^d,\qquad \mathrm{Vol}(Z)\ge 2^d .$$
--
--   The two inclusions and the volume bound are the inputs to the universal lower bound for polytope approximation of zonotopes (Theorem 3.2).
--
--   **Formalization Note** The zonotope and the Lewis matrix are the published definitions of the mission (`zonotope`, `lewis`); the volume is Mathlib's `volume` on `EuclideanSpace ℝ (Fin d)`, valued in $[0,\infty]$.
--
--   Differences from the source:
--   - encoding: Vol(Z) as a real number → Lebesgue measure in ℝ≥0∞; reason: Z is compact so its volume is finite; the inequality is the same
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), Lemma 3.1, p. 11; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Geometry

open MeasureTheory

namespace ZonotopeContainment.AdaptiveSampling.Supplement

/-- Lemma 3.1, p. 11: exact Lewis position, L(V) = I, with nonzero generators gives
B₂ᵈ ⊆ Z ⊆ √d B₂ᵈ and Vol(Z) ≥ 2^d (Lebesgue volume on Euclidean space). -/
theorem lemma_3_1 {d n : ℕ} (v : Fin n → E d) (hv : ∀ i, v i ≠ 0) (hL : lewis v = 1) :
    Metric.closedBall (0 : E d) 1 ⊆ zonotope v ∧
    zonotope v ⊆ Metric.closedBall (0 : E d) (Real.sqrt d) ∧
    (2 : ENNReal) ^ d ≤ volume (zonotope v) := by sorry

end ZonotopeContainment.AdaptiveSampling.Supplement
