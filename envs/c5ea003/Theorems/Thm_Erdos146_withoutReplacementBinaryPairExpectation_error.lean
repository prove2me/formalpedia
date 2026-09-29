-- Prove2me | Theorems.Thm_Erdos146_withoutReplacementBinaryPairExpectation_error
-- name    : Erdos146.withoutReplacementBinaryPairExpectation_error
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:41:48.52016+00:00
-- url     : https://prove2.me/theorems/a03d443b-c1f1-4327-93f9-aa1da47df449
-- title:
--   The without-replacement correction is $o(1)$ (Lemma 5.2)
-- statement:
--   **Lemma 5.2, quantitative form.** The error incurred by replacing without-replacement sampling of the two parents by independent sampling is bounded by $\eta(L)$, which tends to $0$ as the layer size $L$ tends to infinity. Section 6 fixes $L_0 \ge 4$ large enough that $\eta(L) < \delta$ for every $L \ge L_0$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L10557-L10620

import Definitions.Def_erdos146_core2
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.withoutReplacementBinaryPairExpectation_error
    (parentCount oneCount : ℕ)
    (hparents : 2 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (f : Bool → Bool → ℝ)
    (hf : ∀ left right, 0 ≤ f left right ∧ f left right ≤ 1) :
    |withoutReplacementBinaryPairExpectation parentCount oneCount f -
        (∑ left : Bool, ∑ right : Bool,
          independentBinaryPairMass
            ((oneCount : ℝ) / (parentCount : ℝ)) left right *
              f left right)| ≤ 1 / (parentCount : ℝ) := by sorry
