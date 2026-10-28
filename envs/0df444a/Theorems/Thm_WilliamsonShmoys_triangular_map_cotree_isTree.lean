-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_map_cotree_isTree
-- name    : WilliamsonShmoys.triangular_map_cotree_isTree
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T22:16:47.156569+00:00
-- url     : https://prove2.me/theorems/1ab6fe09-7e92-4c3b-a4fb-929ca34843f7
-- title:
--   Euler characteristic two makes the complementary dual a tree
-- statement:
--   This isolates complementary-dual treehood without paths or bags. A contour traversal of the spanning tree, using the vertex rotations, establishes dual connectivity. The dart bijection gives twice the primal edge count equal to three times the face count. Subtracting the spanning tree's |V|−1 edges and using the Euler identity leaves |F|−1 complementary edges, counted with multiplicity. Connectivity then forces a tree, including after passing to the underlying simple graph. In the two-faced triangle, exactly one complementary side remains. This is the classical arbitrary-tree duality described in [Erickson's tree–cotree notes](https://jeffe.cs.illinois.edu/teaching/comptop/2023/notes/10-planar-tree-cotree.html).
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap

theorem WilliamsonShmoys.triangular_map_cotree_isTree
    {V F : Type} [Fintype V] [Fintype F]
    {H : SimpleGraph V} (M : WilliamsonShmoys.TriangularMap H F)
    (heuler : 2 * Fintype.card V = Fintype.card F + 4)
    (R : SimpleGraph V) (hRH : R ≤ H) (hR : R.IsTree) :
    (M.cotree R).IsTree := by sorry
