-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch5_Meromorphic_meromorphic_coeff_transfer_simplePoleSum
-- name    : AnalyticCombinatorics.Ch5.Meromorphic.meromorphic_coeff_transfer_simplePoleSum
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-25T15:35:28.895995+00:00
-- url     : https://prove2.me/theorems/0998b5de-9e96-4055-8440-c17384a0d7ba
-- title:
--   Coefficient error for a supplied finite geometric principal-part decomposition
-- statement:
--   Let $\iota$ be any index type, let $s\subseteq\iota$ be a finite set, let $c,a:\iota\to\mathbb C$, and let $f,g\in\mathbb C[[z]]$. Let $R>0$ be real. Suppose the complex formal multilinear series associated with $g$ has convergence radius strictly greater than $R$, and suppose the following equality holds as formal power series:
--
--   $$f(z)=\sum_{i\in s}\frac{c(i)}{1-a(i)z}+g(z),\qquad
--   \frac{c(i)}{1-a(i)z}=\sum_{n\ge0}c(i)a(i)^n z^n.$$
--
--   Then, as natural $n\to\infty$,
--
--   $$[z^n]f-\sum_{i\in s}c(i)a(i)^n=O(R^{-n}).$$
--
--   The error is complex-valued and the bounding scale is real. The principal-part decomposition is a hypothesis. The finite set may be empty, weights $c(i)$ or $a(i)$ may vanish, and different indices may have the same $a(i)$. Thus the summands need not all have genuine poles. There is no requirement that $R>1$ or that the displayed points be distinct dominant singularities.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch5/Meromorphic/Transfer.lean#L122. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch4_Analytic_Bridge
import Mathlib
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.RadiusLiminf
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Complex.Basic
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
open Filter Asymptotics
open scoped BigOperators ENNReal NNReal PowerSeries Topology

theorem AnalyticCombinatorics.Ch5.Meromorphic.meromorphic_coeff_transfer_simplePoleSum
    {ι : Type*} (s : Finset ι) (c a : ι → ℂ)
    (f g : PowerSeries ℂ) {R : ℝ}
    (hR : 0 < R) (hgR : ENNReal.ofReal R < (PowerSeries.toFMLS g).radius)
    (hfg :
      f =
        (∑ i ∈ s, PowerSeries.C (c i) *
          PowerSeries.rescale (a i) (PowerSeries.invUnitsSub (1 : ℂˣ))) + g) :
    (fun n : ℕ => PowerSeries.coeff (R := ℂ) n f -
      ∑ i ∈ s, c i * (a i) ^ n) =O[atTop] (fun n : ℕ => R⁻¹ ^ n) := by sorry
