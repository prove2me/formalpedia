-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simpleGraph
-- name    : WilliamsonShmoys.finite_simpleGraph
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T23:06:02.618653+00:00
-- url     : https://prove2.me/theorems/ddb9f57a-1868-4270-80e8-a0ccc6bed5cc
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   For a finite vertex type, the type of simple graphs on that vertex type is finite. This supplies the finite search space used by the parent. A proof route is to encode each graph by its set of unordered edges, show this encoding is injective, and use finiteness of the unordered-pair universe. This is independent of planarity and handles vertex types of every finite cardinality, including the empty type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap

theorem WilliamsonShmoys.finite_simpleGraph
    {V : Type} [Fintype V] :
    Finite (SimpleGraph V) := by sorry
