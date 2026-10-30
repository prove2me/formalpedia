-- Prove2me | Theorems.Thm_edgeSet_ncard_strict_of_subset_ne__p2m_a06e74bc_2d14_4a85_b8d6_42f2136549b3_a1
-- name    : edgeSet_ncard_strict_of_subset_ne__p2m_a06e74bc_2d14_4a85_b8d6_42f2136549b3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T23:31:54.085189+00:00
-- url     : https://prove2.me/theorems/4a6660fc-8ad8-4e6d-bdd1-0928470cd6ff
-- title:
--   Proper graph edge inclusion increases finite cardinality
-- statement:
--   For graphs on a finite vertex type, proper inclusion of edge sets strictly increases the edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem edgeSet_ncard_strict_of_subset_ne__p2m_a06e74bc_2d14_4a85_b8d6_42f2136549b3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    {G H : SimpleGraph V}
    (h : Set.Subset G.edgeSet H.edgeSet)
    (hne : G ≠ H) :
    G.edgeSet.ncard < H.edgeSet.ncard := by sorry
