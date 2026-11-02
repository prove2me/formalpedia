-- Prove2me | Theorems.Thm_edge_count_maximal_planar_supergraph__p2m_b64ec28e_2554_405c_95cb_8078e84c56ed_a5
-- name    : edge_count_maximal_planar_supergraph__p2m_b64ec28e_2554_405c_95cb_8078e84c56ed_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:00:08.297341+00:00
-- url     : https://prove2.me/theorems/89b4cf3f-16e9-47dd-8480-7273446aa164
-- title:
--   A planar supergraph with maximum directed adjacency count
-- statement:
--   Among planar supergraphs of a finite graph, there is one with maximum number of directed adjacent vertex pairs; any planar extension with the same count equals it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys Classical

set_option autoImplicit false

theorem edge_count_maximal_planar_supergraph__p2m_b64ec28e_2554_405c_95cb_8078e84c56ed_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K →
        Fintype.card {p : V × V // K.Adj p.1 p.2} ≤
          Fintype.card {p : V × V // H.Adj p.1 p.2}) ∧
      (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K →
        Fintype.card {p : V × V // H.Adj p.1 p.2} =
          Fintype.card {p : V × V // K.Adj p.1 p.2} → K = H) := by sorry
