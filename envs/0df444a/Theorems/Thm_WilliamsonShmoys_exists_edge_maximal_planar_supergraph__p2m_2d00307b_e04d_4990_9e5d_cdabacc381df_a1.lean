-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:32:11.757659+00:00
-- url     : https://prove2.me/theorems/cb39a9bd-ac03-4220-ad24-503e3b68b24e
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every finite planar graph on the given ordered vertex type has a supergraph on the same vertices that admits a planar drawing and is inclusion-maximal among such supergraphs. This follows by maximizing edge count over the finite set of simple graph supergraphs admitting a drawing; strict inclusion strictly increases edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_2d00307b_e04d_4990_9e5d_cdabacc381df_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
