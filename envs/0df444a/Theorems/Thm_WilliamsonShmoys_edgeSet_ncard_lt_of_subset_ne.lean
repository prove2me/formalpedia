-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_lt_of_subset_ne
-- name    : WilliamsonShmoys.edgeSet_ncard_lt_of_subset_ne
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:09:03.815761+00:00
-- url     : https://prove2.me/theorems/3fe9ce64-13b0-4647-8b89-68a66519807b
-- title:
--   A proper inclusion of finite graph edge sets strictly increases cardinality
-- statement:
--   For graphs on a finite vertex type, a proper inclusion of edge sets strictly increases their `Set.ncard`. Finiteness follows because all edges lie among the finitely many unordered pairs of vertices. Apply the finite-cardinality strict-subset result; no planarity assumptions are needed. Equality is excluded explicitly, so the result also covers graphs with empty edge sets whenever the hypotheses permit a proper inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_lt_of_subset_ne
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hsub : Set.Subset G.edgeSet H.edgeSet)
    (hne : G.edgeSet ≠ H.edgeSet) :
    Set.ncard G.edgeSet < Set.ncard H.edgeSet := by sorry
