-- Prove2me | Theorems.Thm_ZeroFreeRRG_Hardcore_coloring_vertex_entropy_increment
-- name    : ZeroFreeRRG.Hardcore.coloring_vertex_entropy_increment
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:30:26.521723+00:00
-- url     : https://prove2.me/theorems/b46c252b-e333-437e-9bd5-2998daf6d91f
-- title:
--   Increasing vertex-entropy increments for coloring
-- statement:
--   Fix $q\ge3$ and a coloring cavity law $\nu$. For each integer $k\ge0$, write $A_k=\mathbb E[V_{k,0}\log V_{k,0}]$ for independent cavity messages. Then $A_{k+1}-A_k\le A_{k+2}-A_{k+1}$. This is the discrete convexity inequality proved via exchangeability and relative-entropy data processing in Lemma 4.27.
-- source:
--   Chen, Wang, and Zhang, Zero-Freeness for Random Regular Graphs up to the Replica Symmetry Breaking Threshold, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1461.pdf, proof of Lemma 4.27, printed p. 34.

import Definitions.Def_ZeroFreeRRG_Hardcore_BetheFunctional
open MeasureTheory

namespace ZeroFreeRRG.Hardcore
theorem coloring_vertex_entropy_increment (q : ℕ) (hq : 3 ≤ q)
    (ν : ProbabilityMeasure ((.potts q : Model).Spin → ℝ)) (hν : ν ∈ cavityLaws (.potts q) 0)
    (k : ℕ) :
    let A := fun n : ℕ => ∫ xs, xlogx (vertexFactor (.potts q) 0 n xs)
      ∂(Measure.pi fun _ : Fin n => (ν : Measure ((.potts q : Model).Spin → ℝ)))
    A (k+1)-A k ≤ A (k+2)-A (k+1) := by sorry
end ZeroFreeRRG.Hardcore
