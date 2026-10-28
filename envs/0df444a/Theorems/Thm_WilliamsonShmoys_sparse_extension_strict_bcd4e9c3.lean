-- Prove2me | Theorems.Thm_WilliamsonShmoys_sparse_extension_strict_bcd4e9c3
-- name    : WilliamsonShmoys.sparse_extension_strict_bcd4e9c3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T00:09:58.438967+00:00
-- url     : https://prove2.me/theorems/264a569b-72b6-4e54-b586-14853783eeea
-- title:
--   The sparse bound forces a strict edge extension
-- statement:
--   If $H$ is a subgraph of $K$, $K$ has the maximal planar edge count, and $H$ satisfies the strict sparse bound, then $K$'s edge set is not contained in $H$'s. Mutual edge-set inclusion would imply equal cardinalities, contradicting the two bounds. The lower bound on the number of vertices ensures subtraction by six does not truncate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.sparse_extension_strict_bcd4e9c3
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hHK : H ≤ K)
    (hcard : K.edgeSet.ncard = 3 * Fintype.card V - 6)
    (hsparse : H.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ¬ K.edgeSet ⊆ H.edgeSet := by sorry
