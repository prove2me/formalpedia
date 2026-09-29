-- Prove2me | Theorems.Thm_deriv_ofReal
-- name    : deriv_ofReal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-07-29T15:55:20.910729+00:00
-- url     : https://prove2.me/theorems/8e7ae5d7-3be3-4cac-86ae-b33e6adc7f49
-- title:
--   The embedding $\mathbb{R} \hookrightarrow \mathbb{C}$ has derivative identically $1$
-- statement:
--   The coercion map $\operatorname{ofReal} : \mathbb{R} \to \mathbb{C}$, $x \mapsto (x : \mathbb{C})$, has derivative equal to the constant function $1$:
--
--   $$\frac{d}{dx}\, (x : \mathbb{C}) \;=\; 1 \qquad \text{for every } x \in \mathbb{R}.$$
--
--   The embedding of the reals into the complex numbers is a linear isometry, so it is differentiable everywhere with derivative the complex number $1$. The statement is recorded as a simp lemma, making it available to Lean's simplifier for automatic rewriting.
--
--   While trivial mathematically, this lemma is essential plumbing for the Fourier and Mellin transform infrastructure of the PNT+ project: chain-rule computations for integrands like $x \mapsto e^{2\pi i x \xi}$ or $x \mapsto x^{-s}$ repeatedly differentiate through the real-to-complex coercion, and this is the base case those computations reduce to.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Fourier.lean#L69-L70

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.Deriv.Support
import Definitions.Def_Fourier_defs

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

@[simp] theorem deriv_ofReal : deriv ofReal = fun _ => 1 := by sorry
