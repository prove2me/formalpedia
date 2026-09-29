-- Prove2me | Definitions.Def_Fourier_defs
-- name    : Fourier_defs
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-07-29T14:48:42.596503+00:00
-- url     : https://prove2.me/theorems/d63534db-3a91-4c93-9117-5770f1e0b8a5
-- title:
--   Fourier-analysis scaffolding: coercion of real-valued to complex-valued functions for Fourier transform lemmas
-- statement:
--   This bundle is the shared setup layer for the Fourier-analytic part of the PNT+ project. It imports the Mathlib theory of Schwartz functions, Fourier transforms and their derivatives, improper integrals, and functions vanishing or bounded at a filter, and opens the corresponding namespaces (`FourierTransform`, `SchwartzMap`, `VectorFourier`, ...).
--
--   **Main definition.**
--
--   - A local coercion instance $\mathrm{Coe}\,(E \to \mathbb{R})\,(E \to \mathbb{C})$, allowing any real-valued function $f : E \to \mathbb{R}$ to be used silently as the complex-valued function $x \mapsto (f(x) : \mathbb{C})$. This keeps statements about Fourier transforms of real smoothing kernels notationally clean.
--
--   **Downstream use.** The lemma section built on this scaffolding provides decay and differentiability facts about Fourier transforms of smooth compactly supported / Schwartz-type functions; these feed the smoothed Chebyshev function analysis and Mellin-transform estimates in the medium-strength prime number theorem proof.
-- source:
--   https://github.com/AlexKontorovich/PrimeNumberTheoremAnd/blob/f55e85551ac10e96d98262a354cfcaac2825f2da/PrimeNumberTheoremAnd/Fourier.lean (definitions vendored from this file)

import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Order.Filter.ZeroAndBoundedAtFilter
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Calculus.Deriv.Support

open FourierTransform Real Complex MeasureTheory Filter Topology BoundedContinuousFunction
  SchwartzMap VectorFourier BigOperators

local instance {E : Type*} : Coe (E → ℝ) (E → ℂ) := ⟨fun f n => f n⟩

section lemmas


end lemmas


