-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_local_edge_extension__p2m_3b9c1b25_36f2_49fb_9760_e5ee7be0caf4_a1
-- name    : WilliamsonShmoys.planar_drawing_local_edge_extension__p2m_3b9c1b25_36f2_49fb_9760_e5ee7be0caf4_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:38:21.599517+00:00
-- url     : https://prove2.me/theorems/7e85fb9b-7eae-4d06-bade-329c1839a3ae
-- title:
--   Add one planar edge between disconnected vertices
-- statement:
--   Given a finite drawing with the stated crossing-free arc conditions and vertices in distinct graph components, add an edge joining those vertices while retaining the drawing property and every existing edge. The disconnectedness hypothesis rules out u = v, so the new edge is a genuine connection between components.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_local_edge_extension__p2m_3b9c1b25_36f2_49fb_9760_e5ee7be0caf4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : WilliamsonShmoys.HasPlanarDrawingOn J)
    (u v : V) (hsep : ¬ Nonempty (J.Walk u v)) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ H : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      J.edgeFinset ⊆ H.edgeFinset ∧
      H.Adj u v := by sorry
