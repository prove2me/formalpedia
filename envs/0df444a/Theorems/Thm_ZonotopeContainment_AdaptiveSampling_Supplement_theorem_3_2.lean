-- Prove2me | Theorems.Thm_ZonotopeContainment_AdaptiveSampling_Supplement_theorem_3_2
-- name    : ZonotopeContainment.AdaptiveSampling.Supplement.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T15:49:21.82756+00:00
-- url     : https://prove2.me/theorems/3f1d519d-f832-46ac-8f6a-6db9751e0fa0
-- title:
--   Theorem 3.2 — universal $\Omega(\sqrt{d/\log(N/d)})$ lower bound for approximating a zonotope by an inscribed polytope on $N$ points
-- statement:
--   There is an absolute constant $c>0$ with the following property. Let $d\ge1$, let $w_1,\dots,w_n\in\mathbb R^d$ span $\mathbb R^d$, and let $Z=\{\sum_i t_iw_i:|t_i|\le1\}$ be the (full-dimensional) zonotope they generate. Let $N\ge 2d$, let $x_1,\dots,x_N\in\mathbb R^d$, let $P=\mathrm{conv}\{x_1,\dots,x_N\}$, and let $s>0$. If
--   $$P\subseteq Z\subseteq sP,$$
--   then
--   $$s\ \ge\ c\,\sqrt{\frac{d}{\log(N/d)}} .$$
--
--   In words, no polytope with $N$ vertices approximates any full-dimensional zonotope better than by a factor of order $\sqrt{d/\log(N/d)}$; for polynomially many vertices this is $\Omega(\sqrt{d/\log d})$, which matches the containment guarantee of the mission's goal theorem. The bound is universal: it holds for every zonotope, not only for one extremal example.
--
--   **Formalization Note** $sP$ is the pointwise dilation of $P$ about the origin, and $\log$ is the natural logarithm; $\log(N/d)\ge\log2>0$.
--
--   Differences from the source:
--   - reading: s ∈ Ω(√(d/log(N/d))) → one absolute constant c > 0 with c·√(d/log(N/d)) ≤ s for every d ≥ 1; reason: an asymptotic Ω bound with a threshold d₀ is equivalent, since s ≥ 1 always holds here (Vol Z ≤ sᵈ Vol P ≤ sᵈ Vol Z) and √(d/log(N/d)) ≤ √(d₀/log 2) for d < d₀, so c can be shrunk to cover small d
--   - reading: "a zonotope" → zonotope whose generators span ℝᵈ; reason: §3 is about full-dimensional zonotopes (abstract and §1.1, "for all full-dimensional zonotopes"; the proof uses exact Lewis position, which exists only for full-dimensional Z); without it the claim is false (a square in a 2-plane of ℝᵈ is its own inscribed polytope with s = 1)
--   - reading: the factor s → a real number s > 0; reason: an approximation factor is positive; without s > 0 the claim is false (s = −1 and a symmetric P = Z satisfy P ⊆ Z ⊆ sP)
--   - generalization: N = poly(d) ≥ 2d → every N ≥ 2d; reason: the stated inequality for all N ≥ 2d specializes to every polynomial N(d) ≥ 2d
--   - generalization: a polytope on N vertices x₁,…,x_N → the convex hull of any N listed points x : Fin N → ℝᵈ (repetitions and non-vertices allowed); reason: a polytope with exactly N vertices is the hull of its N vertices, so every instance of the source is covered
--   - encoding: d implicit (log(N/d) undefined at d = 0) → 1 ≤ d; reason: excludes only the degenerate dimension in which the source's bound is undefined
--   - encoding: Z ⊆ ℝᵈ a zonotope → the origin-centred zonotope {∑ tᵢwᵢ : |tᵢ| ≤ 1} of a finite family w : Fin n → ℝᵈ; reason: this is the paper's definition of a zonotope (eq. (3), p. 2; Lemma 3.1)
-- source:
--   Friedrich Eisenbrand, Thomas Rothvoss, Matteo Russo, Ruben Skorupinski, Optimal Zonotope Containment via Adaptive Gaussian Sampling, STOC 2027 submission #214 (October 2026), Theorem 3.2, p. 12; full-dimensionality from the abstract (p. 1) and §1.1 (p. 3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/214.pdf

import Mathlib
import Definitions.Def_ZonotopeContainment_AdaptiveSampling_Geometry

open scoped Pointwise

namespace ZonotopeContainment.AdaptiveSampling.Supplement

/-- Theorem 3.2, p. 12: one absolute constant c > 0 such that every polytope
P = conv{x₁,…,x_N} with N ≥ 2d and P ⊆ Z ⊆ sP, for a full-dimensional zonotope Z ⊆ ℝᵈ,
has s ≥ c √(d / log(N/d)). -/
theorem theorem_3_2 :
    ∃ c : ℝ, 0 < c ∧
    ∀ (d n N : ℕ) (w : Fin n → E d) (x : Fin N → E d) (s : ℝ),
      1 ≤ d → Submodule.span ℝ (Set.range w) = ⊤ → 2 * d ≤ N → 0 < s →
      convexHull ℝ (Set.range x) ⊆ zonotope w →
      zonotope w ⊆ s • convexHull ℝ (Set.range x) →
      c * Real.sqrt ((d : ℝ) / Real.log ((N : ℝ) / d)) ≤ s := by sorry

end ZonotopeContainment.AdaptiveSampling.Supplement
