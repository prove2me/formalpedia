-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_step__p2m_50dbeb3a_1765_4569_965c_952b7ed019cf_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_step__p2m_50dbeb3a_1765_4569_965c_952b7ed019cf_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:09:34.48753+00:00
-- url     : https://prove2.me/theorems/2e31d8ca-f4cb-4f58-8f6a-f9eae660446e
-- title:
--   Add a drawable edge to connect a disconnected graph
-- statement:
--   A disconnected drawable simple graph on at least three vertices has a drawable strict supergraph on the same vertices. This isolates one bridge step; it does not assert that the extension is already connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension_step__p2m_50dbeb3a_1765_4569_965c_952b7ed019cf_a2
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hNotConn : ¬ H.Connected) :
    ∃ K : SimpleGraph V, H.edgeSet ⊂ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K := by sorry
