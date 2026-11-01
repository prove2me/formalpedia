-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_99da7898_0d3e_41e3_bad9_9b286d32e26c_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_99da7898_0d3e_41e3_bad9_9b286d32e26c_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:34:51.372504+00:00
-- url     : https://prove2.me/theorems/b64ec28e-2554-405c-95cb-8078e84c56ed
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertex type that is maximal among planar supergraphs under edge inclusion. This removes the selection and maximality step from the parent; finiteness of the possible simple graphs gives an independent proof by maximizing edge count. No lower bound on the number of vertices is needed for this step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_99da7898_0d3e_41e3_bad9_9b286d32e26c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
