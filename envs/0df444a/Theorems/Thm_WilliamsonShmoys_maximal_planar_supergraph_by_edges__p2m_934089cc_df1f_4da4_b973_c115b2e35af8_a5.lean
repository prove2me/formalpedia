-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_by_edges__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a5
-- name    : WilliamsonShmoys.maximal_planar_supergraph_by_edges__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:28:09.513543+00:00
-- url     : https://prove2.me/theorems/270af860-12f4-4e91-b85d-8c33e87aac59
-- title:
--   Maximum-edge planar supergraph
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph containing it whose edge count is at least that of every other planar supergraph containing it. The claim isolates finite extremal selection; it can be proved by maximizing edge count over the finite, nonempty family of eligible graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_by_edges__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : Fintype K.edgeSet := Fintype.ofFinite _;
       ∀ L : SimpleGraph V, H ≤ L → HasPlanarDrawingOn L →
         (letI : Fintype L.edgeSet := Fintype.ofFinite _;
          L.edgeFinset.card ≤ K.edgeFinset.card)) := by sorry
