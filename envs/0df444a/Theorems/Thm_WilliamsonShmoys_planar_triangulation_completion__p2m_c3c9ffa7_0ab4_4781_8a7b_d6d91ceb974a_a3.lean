-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_completion__p2m_c3c9ffa7_0ab4_4781_8a7b_d6d91ceb974a_a3
-- name    : WilliamsonShmoys.planar_triangulation_completion__p2m_c3c9ffa7_0ab4_4781_8a7b_d6d91ceb974a_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:07:50.012094+00:00
-- url     : https://prove2.me/theorems/d8025907-d5c3-4b74-a462-234358441f90
-- title:
--   Planar drawing has a triangulation completion with exact edge count
-- statement:
--   Every finite graph with a planar drawing and at least three vertices has a planar supergraph on the same vertex set with exactly 3|V|−6 edges. This child removes the maximality-to-edge-count step from the parent and isolates the augmentation and Euler-counting argument. Its independent proof route is to extend a planar drawing by admissible edges until its faces are triangular, then count face-edge incidences and apply Euler’s formula. The remaining core is formalizing that extension and face argument, including disconnected initial drawings and the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_completion__p2m_c3c9ffa7_0ab4_4781_8a7b_d6d91ceb974a_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hn : 3 <= Fintype.card V) :
    Exists fun (L : SimpleGraph V) => Exists fun (dL : DecidableRel L.Adj) =>
      WilliamsonShmoys.HasPlanarDrawingOn L /\
      K.edgeFinset ⊆ L.edgeFinset /\
      L.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
