-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension_edge_lower_bound__p2m_77d34f95_c28b_41e7_bbec_f475d739e777_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension_edge_lower_bound__p2m_77d34f95_c28b_41e7_bbec_f475d739e777_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:47:13.862206+00:00
-- url     : https://prove2.me/theorems/ea7a71ed-13b1-4c29-adb9-6de531e96387
-- title:
--   Planar triangulation extension edge lower bound
-- statement:
--   Any crossing-free drawing on a finite ordered vertex type with at least three vertices can be extended, on the same vertex type, to a drawable graph containing all its edges and having at least 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension_edge_lower_bound__p2m_77d34f95_c28b_41e7_bbec_f475d739e777_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hcard : 3 <= Fintype.card V) :
    ∃ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
      K.edgeFinset ⊆ L.edgeFinset ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 <= L.edgeFinset.card := by sorry
