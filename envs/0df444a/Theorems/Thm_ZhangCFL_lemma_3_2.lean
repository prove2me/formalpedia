-- Prove2me | Theorems.Thm_ZhangCFL_lemma_3_2
-- name    : ZhangCFL.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:50:01.951767+00:00
-- url     : https://prove2.me/theorems/bfe0ae53-d3f1-4651-ac1a-85ee31add1da
-- title:
--   Lemma 3.2: suprema and partial infima of convex functions
-- statement:
--   Let $X$ and $Y$ be convex subsets of real vector spaces and let $f:X\times Y\to\mathbb R$.
--
--   1. If $f(\cdot,y)$ is convex on $X$ for every $y\in Y$, then $x\mapsto\sup_{y\in Y}f(x,y)$ is convex on $X$; if $f(\cdot,y)$ is concave for every $y\in Y$, then $x\mapsto\inf_{y\in Y}f(x,y)$ is concave on $X$.
--   2. If $f$ is jointly convex on $X\times Y$, then $x\mapsto\inf_{y\in Y}f(x,y)$ is convex on $X$; if $f$ is jointly concave on $X\times Y$, then $x\mapsto\sup_{y\in Y}f(x,y)$ is concave on $X$.
--
--   The suprema and infima are allowed to be $\pm\infty$, and convexity of an extended-real-valued function $g$ means
--
--   $$
--   g(a x_1 + b x_2) \le a\,g(x_1) + b\,g(x_2), \qquad x_1,x_2\in X,\ a,b\ge 0,\ a+b=1
--   $$
--
--   (reversed for concavity). This lemma is how the variational formulas of Theorem 3.3 transfer convexity and concavity from simpler trace functions to $\Upsilon_{p,s}$ and $\Psi_{p,q,s}$.
--
--   **Formalization Note** The supremum and infimum are `⨆ y ∈ Y` and `⨅ y ∈ Y` in `EReal`; no boundedness is assumed. Mathlib's conventions $0\cdot(\pm\infty)=0$ apply at the endpoints $a=0$ or $b=0$, where both sides then coincide.
--
--   Differences from the source:
--   - encoding: f : X × Y → ℝ → f : E → F → ℝ on the ambient spaces; reason: only the values on X × Y enter the hypotheses and conclusions
--   - encoding: sup and inf as real-valued functions with convexity in the usual sense → sup and inf in EReal with convexity as the two-point inequality; reason: the source does not assume the sup or inf finite, and the two-point inequality is the usual definition of convexity for extended-real functions; on real-valued sup or inf it is ConvexOn
--   - encoding: vector spaces → real vector spaces; reason: convexity refers to real convex combinations
-- source:
--   Zhang, From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture, arXiv:1811.01205v2, Lemma 3.2, p.7 (proof pp.7–8)

import Mathlib

namespace ZhangCFL

/-- Zhang, *From Wigner-Yanase-Dyson conjecture to Carlen-Frank-Lieb conjecture*,
arXiv:1811.01205v2, Lemma 3.2, p.7: let `X, Y` be convex subsets of real vector spaces and
`f : X × Y → ℝ`.
(1) If `f(·, y)` is convex (resp. concave) for every `y ∈ Y`, then `x ↦ sup_{y∈Y} f(x, y)`
(resp. `x ↦ inf_{y∈Y} f(x, y)`) is convex (resp. concave).
(2) If `f` is jointly convex (resp. concave) on `X × Y`, then `x ↦ inf_{y∈Y} f(x, y)`
(resp. `x ↦ sup_{y∈Y} f(x, y)`) is convex (resp. concave).

**Formalization Note.** `f` is a function `E → F → ℝ` whose values off `X × Y` play no role.
The supremum and infimum are taken in `EReal` (`⨆ y ∈ Y, (f x y : EReal)`), so they may be
`±∞` and no boundedness is assumed. Convexity of the `EReal`-valued function `g` on `X` is
written as the two-point inequality `g (a • x₁ + b • x₂) ≤ a * g x₁ + b * g x₂` for
`x₁, x₂ ∈ X`, `a, b ≥ 0`, `a + b = 1` (reversed for concavity). -/
theorem lemma_3_2 {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (X : Set E) (Y : Set F) (hX : Convex ℝ X) (hY : Convex ℝ Y) (f : E → F → ℝ) :
    ((∀ y ∈ Y, ConvexOn ℝ X (fun x => f x y)) →
      ∀ x₁ ∈ X, ∀ x₂ ∈ X, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        (⨆ y ∈ Y, (f (a • x₁ + b • x₂) y : EReal)) ≤
          (a : EReal) * (⨆ y ∈ Y, (f x₁ y : EReal)) +
            (b : EReal) * (⨆ y ∈ Y, (f x₂ y : EReal))) ∧
    ((∀ y ∈ Y, ConcaveOn ℝ X (fun x => f x y)) →
      ∀ x₁ ∈ X, ∀ x₂ ∈ X, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        (a : EReal) * (⨅ y ∈ Y, (f x₁ y : EReal)) +
            (b : EReal) * (⨅ y ∈ Y, (f x₂ y : EReal)) ≤
          (⨅ y ∈ Y, (f (a • x₁ + b • x₂) y : EReal))) ∧
    (ConvexOn ℝ (X ×ˢ Y) (fun z => f z.1 z.2) →
      ∀ x₁ ∈ X, ∀ x₂ ∈ X, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        (⨅ y ∈ Y, (f (a • x₁ + b • x₂) y : EReal)) ≤
          (a : EReal) * (⨅ y ∈ Y, (f x₁ y : EReal)) +
            (b : EReal) * (⨅ y ∈ Y, (f x₂ y : EReal))) ∧
    (ConcaveOn ℝ (X ×ˢ Y) (fun z => f z.1 z.2) →
      ∀ x₁ ∈ X, ∀ x₂ ∈ X, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        (a : EReal) * (⨆ y ∈ Y, (f x₁ y : EReal)) +
            (b : EReal) * (⨆ y ∈ Y, (f x₂ y : EReal)) ≤
          (⨆ y ∈ Y, (f (a • x₁ + b • x₂) y : EReal))) := by sorry

end ZhangCFL
