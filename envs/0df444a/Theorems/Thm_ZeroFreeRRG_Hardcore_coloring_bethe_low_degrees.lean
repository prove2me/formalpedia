-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_bethe_low_degrees
-- name    : ZeroFreeRRG.Hardcore.coloring_bethe_low_degrees
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:11:37.289893+00:00
-- url     : https://prove2.me/theorems/fa585a0c-4b8b-4bb6-9088-47f6748d7c5c
-- title:
--   Coloring Bethe functional at degrees zero and one
-- statement:
--   Let $q\ge2$ and let $\nu$ be a nontrivial coloring cavity law with uniform barycenter. Then the real-degree Bethe functional satisfies $\mathcal B_{0,0}(\nu)=0$ and $\mathcal B_{1,0}(\nu)<0$. These are the endpoint statements in the degree-convexity part of Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Lemma 4.27, printed pp. 34–35.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem coloring_bethe_low_degrees (q : ℕ) (hq : 2 ≤ q)
    (ν : ProbabilityMeasure ((.potts q : Model).Spin → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) 0) (hne : ν ≠ diracPi (.potts q) 0) :
    betheR (.potts q) 0 0 ν = 0 ∧ betheR (.potts q) 0 1 ν < 0 := by sorry
end ZeroFreeRRG.Hardcore
