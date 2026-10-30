-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_connected__p2m_39e1387e_c6b4_4e32_ad1b_235228b03693_a4
-- name    : WilliamsonShmoys.maximal_planar_graph_connected__p2m_39e1387e_c6b4_4e32_ad1b_235228b03693_a4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:32:28.37258+00:00
-- url     : https://prove2.me/theorems/8c53f87a-b244-43b9-9258-2c83805c4d13
-- title:
--   A maximal drawable graph connects every pair of distinct vertices
-- statement:
--   If a drawable graph on a finite ordered vertex type has no strict drawable supergraph, then every two distinct vertices are connected by a path.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_connected__p2m_39e1387e_c6b4_4e32_ad1b_235228b03693_a4
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L)
    {u v : V} (huv : u ≠ v) :
    L.Reachable u v := by sorry
