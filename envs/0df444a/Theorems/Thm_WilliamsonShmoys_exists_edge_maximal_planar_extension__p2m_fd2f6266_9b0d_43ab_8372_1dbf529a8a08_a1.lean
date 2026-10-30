-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T08:55:46.459047+00:00
-- url     : https://prove2.me/theorems/06af0a91-094c-4aa1-93f1-69966cc94cab
-- title:
--   Finite edge-maximal drawable extension
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_fd2f6266_9b0d_43ab_8372_1dbf529a8a08_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K ≤ N := by sorry
