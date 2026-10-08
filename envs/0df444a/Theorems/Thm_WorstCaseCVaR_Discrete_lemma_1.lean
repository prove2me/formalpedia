-- Prove2me | Theorems.Thm_WorstCaseCVaR_Discrete_lemma_1
-- name    : WorstCaseCVaR.Discrete.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:58:53.729002+00:00
-- url     : https://prove2.me/theorems/01031d5b-c8c4-4f51-8e48-03a153fa3c05
-- title:
--   Lemma 1 — minimax equality for convex–concave functions on compact convex sets
-- statement:
--   Let $\mathcal X \subseteq \mathbb R^n$ and $\mathcal Y \subseteq \mathbb R^m$ be nonempty compact convex sets, and let $\phi : \mathbb R^n \times \mathbb R^m \to \mathbb R$ be such that
--
--   1. for each $y \in \mathcal Y$, $x \mapsto \phi(x,y)$ is convex and lower semicontinuous on $\mathcal X$;
--   2. for each $x \in \mathcal X$, $y \mapsto \phi(x,y)$ is concave and upper semicontinuous on $\mathcal Y$.
--
--   Then $\phi$ has a saddle point $(x_0,y_0) \in \mathcal X \times \mathcal Y$:
--   $$\phi(x_0,y) \le \phi(x_0,y_0) \le \phi(x,y_0) \qquad \text{for all } x \in \mathcal X,\ y \in \mathcal Y,$$
--   and therefore
--   $$\min_{x\in\mathcal X}\max_{y\in\mathcal Y}\phi(x,y) = \max_{y\in\mathcal Y}\min_{x\in\mathcal X}\phi(x,y),$$
--   with every minimum and maximum attained.
--
--   This is the minimax theorem of Ky Fan (1953) in the form the paper quotes; it is the tool that exchanges the minimization over the threshold $\alpha$ with the maximization over the distribution $\pi$.
--
--   **Formalization Note** The paper states Lemma 1 without the two semicontinuity conditions; they are added because without them the minima and maxima need not exist (on $\mathcal X=\mathcal Y=[0,1]$, $\phi(x,y)=x$ for $x>0$ and $\phi(0,y)=1$ is convex in $x$ and constant in $y$, and $\min_x\max_y\phi$ is not attained). The conclusion is the saddle-point form, which is equivalent to the attained min–max equality. Mission 1 of this series states the same lemma under the name `WorstCaseCVaR.Mixture.lemma_1`.
-- source:
--   Zhu & Fukushima, Worst-Case Conditional Value-at-Risk with Application to Robust Portfolio Management, Oper. Res. 57(5), 2009, p. 1157, Lemma 1 (Fan 1953)

import Mathlib

namespace WorstCaseCVaR.Discrete

/-- Lemma 1, Zhu & Fukushima (2009), p. 1157 (Fan 1953): for nonempty compact convex
`𝒳 ⊆ ℝⁿ`, `𝒴 ⊆ ℝᵐ` and `φ(x, y)` convex and lower semicontinuous in `x` for each `y ∈ 𝒴`, concave
and upper semicontinuous in `y` for each `x ∈ 𝒳`, `φ` has a saddle point `(x₀, y₀)` on `𝒳 × 𝒴`;
equivalently, `min_{x ∈ 𝒳} max_{y ∈ 𝒴} φ(x, y) = max_{y ∈ 𝒴} min_{x ∈ 𝒳} φ(x, y)` with every
minimum and maximum attained. The semicontinuity hypotheses are not printed in the paper; they
are needed for the minima and maxima to exist. -/
theorem lemma_1 {n m : ℕ} (X : Set (Fin n → ℝ)) (Y : Set (Fin m → ℝ))
    (hXne : X.Nonempty) (hXc : IsCompact X) (hXcv : Convex ℝ X)
    (hYne : Y.Nonempty) (hYc : IsCompact Y) (hYcv : Convex ℝ Y)
    (φ : (Fin n → ℝ) → (Fin m → ℝ) → ℝ)
    (hconv : ∀ y ∈ Y, ConvexOn ℝ X (fun x => φ x y))
    (hconc : ∀ x ∈ X, ConcaveOn ℝ Y (fun y => φ x y))
    (hlsc : ∀ y ∈ Y, LowerSemicontinuousOn (fun x => φ x y) X)
    (husc : ∀ x ∈ X, UpperSemicontinuousOn (fun y => φ x y) Y) :
    ∃ x₀ ∈ X, ∃ y₀ ∈ Y, ∀ x ∈ X, ∀ y ∈ Y, φ x₀ y ≤ φ x₀ y₀ ∧ φ x₀ y₀ ≤ φ x y₀ := by sorry

end WorstCaseCVaR.Discrete
