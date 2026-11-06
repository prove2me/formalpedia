-- Prove2me | Theorems.Thm_YuStrategic_Optimality_lemma_5_5
-- name    : YuStrategic.Optimality.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T20:23:08.717538+00:00
-- url     : https://prove2.me/theorems/739b57d7-35d5-4676-ab70-f8ffbf9b1f65
-- title:
--   Lemma 5.5 — an admissible universally measurable kernel is the image of Lebesgue measure under $f(\cdot,y)$
-- statement:
--   Let $\mathbb X,\mathbb A$ carry the Borel-space MDP with analytic constraint graph $\Gamma$, let $Y$ be a Borel space, $s:Y\to\mathbb X$ a Borel measurable map, and $\nu(da\mid y)$ a universally measurable stochastic kernel on $\mathbb A$ given $Y$ with $\nu(A(s(y))\mid y)=1$ for all $y$. Then there is a universally measurable function $f:[0,1]\times Y\to\mathbb A$ such that, for all $y\in Y$,
--   $$f(\theta,y)\in A(s(y))\quad\forall\,\theta\in[0,1],\qquad \nu(da\mid y)=(\lambda\circ\phi_y^{-1})(da),$$
--   where $\lambda$ is Lebesgue measure on $[0,1]$ and $\lambda\circ\phi_y^{-1}$ is the image measure of $\lambda$ under $\phi_y:=f(\cdot,y)$.
--
--   The paper states this for the kernels $\mu_n(da_n\mid\hat h_n)$ of a structured policy $\pi\in\Pi_{\mathcal C}$, with $\hat h_n$ ranging over the variables the policy may use (which include $x_n$); that is the case $Y=\hat H_n$, $s(\hat h_n)=x_n$, $\nu=\mu_n$, for each $n\ge0$. It is the randomization device behind Theorem 3.2: an admissible randomized decision is an admissible deterministic decision driven by a uniform variable.
--
--   Differences from the source:
--   - generalization: the kernels $\mu_n(da_n\mid\hat h_n)$ of a policy $\pi\in\Pi_{\mathcal C}$, $n\ge0$ → any universally measurable kernel $\nu$ on $\mathbb A$ given a Borel space $Y$ with $\nu(A(s(y))\mid y)=1$ for a Borel map $s$; reason: the page's case is $Y=\hat H_n$, $s(\hat h_n)=x_n$, $\nu=\mu_n$, applied for each $n$
--   - encoding: $\mu_n=\lambda\circ\phi^{-1}_{\hat h_n}$ as measures → $\nu(B\mid y)=\lambda\{\theta\mid f(\theta,y)\in B\}$ for every Borel $B\subseteq\mathbb A$; reason: this is the definition of the image measure, stated setwise because Mathlib's `Measure.map` is zero for maps it cannot see are measurable; the set is universally measurable and its outer measure is the completion's value
--   - encoding: analytic sets as the empty set or images of Borel subsets of Polish spaces under Borel maps (p. 5) → Mathlib's `AnalyticSet` (empty or a continuous image of the Baire space); reason: the two agree for subsets of a Borel space (Bertsekas–Shreve Prop. 7.41)
--   - generalization: the model includes a lower semianalytic one-stage cost $c$ → the model has no cost; reason: the statement does not involve $c$
-- source:
--   Yu, arXiv:2206.06492v3, Lemma 5.5, p. 29

import Mathlib
import Definitions.Def_BertsekasShreve_AnalyticSelection_BorelSpace
import Definitions.Def_BertsekasShreve_BorelInfinite_Analytic
import Definitions.Def_BertsekasShreve_BorelInfinite_Policy
import Definitions.Def_YuStrategic_Optimality_Model

namespace YuStrategic.Optimality

open MeasureTheory BertsekasShreve.AnalyticSelection BertsekasShreve.BorelInfinite

/-- **Lemma 5.5** (Yu, arXiv:2206.06492v3, p. 29), for a single kernel over a general index space.
Let `Y` be a Borel space, `s : Y → X` a Borel measurable map, and `ν(da | y)` a universally
measurable stochastic kernel on `A` given `Y` with `ν(A(s(y)) | y) = 1` for all `y`. Then there is
a universally measurable function `f : [0, 1] × Y → A` such that for all `y ∈ Y`,
`f(θ, y) ∈ A(s(y))` for all `θ ∈ [0, 1]`, and `ν(da | y) = (λ ∘ φ_y⁻¹)(da)`, the image measure of the
Lebesgue measure `λ` on `[0, 1]` under `φ_y := f(·, y)`.

The page's Lemma 5.5 is the case `Y = Ĥₙ` (the variables `ĥₙ` a structured policy `π ∈ Π_C` may use,
which include `xₙ`), `s(ĥₙ) = xₙ` and `ν = μₙ`, applied for each `n ≥ 0`.

**Formalization Note.** The image measure is stated setwise,
`ν(B | y) = λ{θ | f(θ, y) ∈ B}` for every Borel `B ⊆ A`; the set `{θ | f(θ, y) ∈ B}` is universally
measurable, and Mathlib's evaluation of `volume` on it (outer measure) is the completion's value.
`[0, 1] × Y` carries the product σ-algebra, which is its Borel σ-algebra. -/
theorem lemma_5_5 {X A : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [IsBorelSpace X] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A] [IsBorelSpace A]
    {Y : Type} [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y] [IsBorelSpace Y]
    (M : Model X A) (s : Y → X) (hs : Measurable s) (ν : UKernel Y A)
    (hν : ∀ y, ν.toFun y (M.adm (s y)) = 1) :
    ∃ f : unitInterval × Y → A, BertsekasShreve.BorelInfinite.IsUniversallyMeasurableFun f ∧
      (∀ (θ : unitInterval) (y : Y), f (θ, y) ∈ M.adm (s y)) ∧
      ∀ (y : Y) (B : Set A), MeasurableSet B →
        ν.toFun y B = (volume : Measure unitInterval) {θ | f (θ, y) ∈ B} := by sorry

end YuStrategic.Optimality
