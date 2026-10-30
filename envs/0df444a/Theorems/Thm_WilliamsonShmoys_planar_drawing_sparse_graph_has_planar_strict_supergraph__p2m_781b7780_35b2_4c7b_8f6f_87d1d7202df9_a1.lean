-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_sparse_graph_has_planar_strict_supergraph__p2m_781b7780_35b2_4c7b_8f6f_87d1d7202df9_a1
-- name    : WilliamsonShmoys.planar_drawing_sparse_graph_has_planar_strict_supergraph__p2m_781b7780_35b2_4c7b_8f6f_87d1d7202df9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T18:16:13.762986+00:00
-- url     : https://prove2.me/theorems/7e1e673f-b342-4c9b-bd1e-cc03f8c5f53a
-- title:
--   Sparse drawable graphs admit a drawable strict supergraph
-- statement:
--   If a finite drawable simple graph has at least three vertices and fewer than 3n−6 edges, then one can add edges on the same vertex set to obtain a strictly larger drawable simple graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_sparse_graph_has_planar_strict_supergraph__p2m_781b7780_35b2_4c7b_8f6f_87d1d7202df9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hCard : 3 <= Fintype.card V)
    (hT : WilliamsonShmoys.HasPlanarDrawingOn T)
    (hSparse : T.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ R : SimpleGraph V,
      (∀ u v, T.Adj u v → R.Adj u v) ∧
      R ≠ T ∧
      WilliamsonShmoys.HasPlanarDrawingOn R := by sorry
