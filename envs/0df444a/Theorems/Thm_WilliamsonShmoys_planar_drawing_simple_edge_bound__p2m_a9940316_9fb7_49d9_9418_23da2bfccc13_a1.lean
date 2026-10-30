-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound__p2m_a9940316_9fb7_49d9_9418_23da2bfccc13_a1
-- name    : WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_a9940316_9fb7_49d9_9418_23da2bfccc13_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:40:52.318437+00:00
-- url     : https://prove2.me/theorems/30c809bc-d869-43a8-8404-fcf85ec28b0f
-- title:
--   Simple planar edge bound
-- statement:
--   A connected simple planar graph with at least three vertices has at most 3n − 6 edges, expressed without subtraction as m + 6 ≤ 3n. This removes the planar sparsity estimate from the parent. A proof route uses Euler's formula together with the face-boundary incidence count: simplicity and n ≥ 3 ensure every facial boundary walk has length at least three, while each edge is counted twice. Trees are handled by the same incidence count, whose single facial walk has length 2m ≥ 4 under the stated hypotheses.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_simple_edge_bound__p2m_a9940316_9fb7_49d9_9418_23da2bfccc13_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) : (T.edgeSet.ncard : ℤ) + 6 ≤ 3 * (Fintype.card V : ℤ) := by sorry
