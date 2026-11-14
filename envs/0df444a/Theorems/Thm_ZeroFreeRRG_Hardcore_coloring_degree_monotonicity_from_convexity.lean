-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_degree_monotonicity_from_convexity
-- name    : ZeroFreeRRG.Hardcore.coloring_degree_monotonicity_from_convexity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:15:42.841237+00:00
-- url     : https://prove2.me/theorems/5ba5fb86-7cfb-45ea-93a1-1b4a5f6579cc
-- title:
--   Coloring degree monotonicity from convexity
-- statement:
--   Let $q\ge2$ and let $\nu$ be a nontrivial coloring cavity law whose interpolated Bethe functional is convex on the nonnegative degrees. If the functional is nonpositive at degree $r$, then it is nonpositive at every degree $s\in[0,r]$. The convexity premise is stated explicitly; this result supplies the monotonicity step in Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed pp. 34–35.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open scoped Classical
open Set

namespace ZeroFreeRRG.Hardcore
theorem coloring_degree_monotonicity_from_convexity (q : ℕ) (hq : 2 ≤ q)
    (ν : MeasureTheory.ProbabilityMeasure ((.potts q : Model).Spin → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) 0) (hne : ν ≠ diracPi (.potts q) 0)
    (hconv : ConvexOn ℝ (Ici 0) (fun t => betheR (.potts q) 0 t ν))
    (r s : ℝ) (hs : 0 ≤ s) (hsr : s ≤ r) (hr : betheR (.potts q) 0 r ν ≤ 0) :
    betheR (.potts q) 0 s ν ≤ 0 := by sorry
end ZeroFreeRRG.Hardcore
