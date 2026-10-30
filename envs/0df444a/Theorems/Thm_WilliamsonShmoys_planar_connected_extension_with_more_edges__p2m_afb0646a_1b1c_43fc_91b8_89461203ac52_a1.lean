-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_extension_with_more_edges__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1
-- name    : WilliamsonShmoys.planar_connected_extension_with_more_edges__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:18:01.777466+00:00
-- url     : https://prove2.me/theorems/0a5e5754-59b8-4ecb-aaba-c4a2c7627c49
-- title:
--   Connected planar extension with additional edges
-- statement:
--   Extend a disconnected planar drawing on at least three vertices to a connected planar supergraph on the same vertices with strictly more edges. This isolates the geometric work from the target's requirement to exhibit a particular new cross-component edge. The hypotheses retain the vertex-cardinality and disconnectedness conditions; the three-vertex lower bound is the standard threshold for maximal planar extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_connected_extension_with_more_edges__p2m_afb0646a_1b1c_43fc_91b8_89461203ac52_a1 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : HasPlanarDrawingOn G) (hCard : 3 ≤ Fintype.card V) (hNotConnected : ¬ G.Connected) : ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧ G.edgeSet.ncard < H.edgeSet.ncard ∧ H.Connected := by sorry
