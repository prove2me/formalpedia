-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_simple_graph_universe__p2m_c7758452_5c88_40df_afb8_de29ffe25650_a1
-- name    : WilliamsonShmoys.finite_simple_graph_universe__p2m_c7758452_5c88_40df_afb8_de29ffe25650_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:15:06.881865+00:00
-- url     : https://prove2.me/theorems/3e0d78c4-3136-4162-a2db-e0c0994faf74
-- title:
--   Finiteness of simple graphs on a finite vertex type
-- statement:
--   The collection of all simple graphs on a finite linearly ordered vertex type is finite.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.finite_simple_graph_universe__p2m_c7758452_5c88_40df_afb8_de29ffe25650_a1
    {V : Type} [Fintype V] [LinearOrder V] :
    (Set.univ : Set (SimpleGraph V)).Finite := by
  sorry
