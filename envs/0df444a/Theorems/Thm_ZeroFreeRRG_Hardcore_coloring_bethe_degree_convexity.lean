-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_bethe_degree_convexity
-- name    : ZeroFreeRRG.Hardcore.coloring_bethe_degree_convexity
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:21:03.921345+00:00
-- url     : https://prove2.me/theorems/ddfef865-1a48-440f-8352-77f7fc0381e8
-- title:
--   Degree convexity of the coloring Bethe functional
-- statement:
--   Fix $q\ge3$. For every coloring cavity law $\nu$ with uniform barycenter, the real-degree Bethe functional $s\mapsto\mathcal B_{s,0}(\nu)$ is convex on $[0,\infty)$. The point-mass law is included. This isolates the information-theoretic convexity step in Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, Lemma 4.27, printed pp. 34–35.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem coloring_bethe_degree_convexity (q : ℕ) (hq : 3 ≤ q)
    (ν : ProbabilityMeasure ((.potts q : Model).Spin → ℝ)) (hν : ν ∈ cavityLaws (.potts q) 0) :
    ConvexOn ℝ (Set.Ici 0) (fun s => betheR (.potts q) 0 s ν) := by sorry
end ZeroFreeRRG.Hardcore
