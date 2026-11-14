-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_vertex_factor_mean_one
-- name    : ZeroFreeRRG.Hardcore.coloring_vertex_factor_mean_one
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:44:00.948827+00:00
-- url     : https://prove2.me/theorems/2cc2b826-bf64-4f14-85f3-2105edd58a7f
-- title:
--   Coloring vertex factor has mean one
-- statement:
--   For $q\ge3$, $d\ge0$, and independent messages from a coloring cavity law, the expected vertex factor $V_{d,0}$ equals one. Thus it is the density of a probability law relative to the product cavity law, as used in the entropy representation in Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 34.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem coloring_vertex_factor_mean_one (q d : ℕ) (hq : 3 ≤ q) (ν : ProbabilityMeasure (Fin q → ℝ))
    (hν : ν ∈ cavityLaws (.potts q) 0) :
    (∫ xs, vertexFactor (.potts q) 0 d xs
      ∂(Measure.pi fun _ : Fin d => (ν : Measure (Fin q → ℝ)))) = 1 := by sorry
end ZeroFreeRRG.Hardcore
