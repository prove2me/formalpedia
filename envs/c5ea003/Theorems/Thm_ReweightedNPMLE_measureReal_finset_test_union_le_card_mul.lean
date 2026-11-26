-- Prove2me | Theorems.Thm_ReweightedNPMLE_measureReal_finset_test_union_le_card_mul
-- name    : ReweightedNPMLE.measureReal_finset_test_union_le_card_mul
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:41:46.372861+00:00
-- url     : https://prove2.me/theorems/50a97122-8219-4442-abec-0476548ed88a
-- title:
--   A finite union bound in real-valued measure notation
-- statement:
--   Let $\mu$ be a measure, $N$ a finite index set, and $T_r$ arbitrary sets. Write $\mu_{\mathbb R}(A)=(\mu(A)).\mathrm{toReal}$, so finite measure values are unchanged and an infinite value is represented by zero. If $b\ge0$ and $\mu_{\mathbb R}(T_r)\le b$ for every $r\in N$, then
--   $$\mu_{\mathbb R}\!\left(\bigcup_{r\in N}T_r\right)\le |N|b.$$
--   When $\mu$ is finite, this is the usual finite-union bound, including for outer-measure interpretations of nonmeasurable sets. No measurability assumption on the individual test sets is required.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/FiniteNet.lean#L143-L164

import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_Hellinger

/-!
# Finite-net likelihood testing

This file isolates the probability-theoretic union-bound step in the proof of
the paper's uniform near-MLE theorem.  The analytic construction of a
Gaussian-mixture net and the fixed-density likelihood-ratio estimate enter as
explicit hypotheses; the passage from those pointwise estimates to one event
which controls every candidate is proved here.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.measureReal_finset_test_union_le_card_mul
    {Ω ι : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : Finset ι) (test : ι → Set Ω) (b : ℝ)
    (hb : 0 ≤ b) (htest : ∀ p ∈ N, μ.real (test p) ≤ b) :
    μ.real (⋃ p ∈ N, test p) ≤ N.card * b := by sorry
