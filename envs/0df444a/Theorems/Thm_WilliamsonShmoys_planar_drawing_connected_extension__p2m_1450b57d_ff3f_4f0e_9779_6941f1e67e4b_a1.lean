-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension__p2m_1450b57d_ff3f_4f0e_9779_6941f1e67e4b_a1
-- name    : WilliamsonShmoys.planar_drawing_connected_extension__p2m_1450b57d_ff3f_4f0e_9779_6941f1e67e4b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:03:23.849897+00:00
-- url     : https://prove2.me/theorems/cbf42281-ecc6-434c-9482-612de70e0a26
-- title:
--   Connect a finite planar drawing without losing edges
-- statement:
--   For a finite ordered vertex type with at least three vertices, any graph with the specified crossing-free drawing has a connected planar supergraph on the same vertices whose edge count is at least the original graph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_extension__p2m_1450b57d_ff3f_4f0e_9779_6941f1e67e4b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    ∃ H : SimpleGraph V, K ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      K.edgeFinset.card ≤ H.edgeFinset.card := by sorry
