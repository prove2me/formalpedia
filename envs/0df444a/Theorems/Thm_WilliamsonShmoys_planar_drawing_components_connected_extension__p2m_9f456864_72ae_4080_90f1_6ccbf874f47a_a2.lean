-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_components_connected_extension__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
-- name    : WilliamsonShmoys.planar_drawing_components_connected_extension__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T19:09:00.092344+00:00
-- url     : https://prove2.me/theorems/343e7634-bf89-4d0d-a54b-557d3af37c62
-- title:
--   Connect components of a planar drawing by adding edges
-- statement:
--   Extend the supplied drawing to a connected supergraph on the same finite vertex set. The cardinality hypothesis ensures the vertex type is nonempty. A proof route is to connect drawing components one at a time with arcs in the complement of the finite embedded graph, preserving the existing drawing. This removes the disconnected-graph case from the parent; the remaining work is formalizing that planar topological extension for the exact arc predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_components_connected_extension__p2m_9f456864_72ae_4080_90f1_6ccbf874f47a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
