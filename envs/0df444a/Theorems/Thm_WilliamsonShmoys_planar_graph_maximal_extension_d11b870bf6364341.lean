-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_maximal_extension_d11b870bf6364341
-- name    : WilliamsonShmoys.planar_graph_maximal_extension_d11b870bf6364341
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T03:14:06.790118+00:00
-- url     : https://prove2.me/theorems/7374d3a6-3f1d-454b-bde5-d40172d2bac8
-- title:
--   Finite drawable extension to an inclusion-maximal graph
-- statement:
--   Every finite graph with a crossing-free drawing is contained in a drawable supergraph on the same vertex type that is maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_maximal_extension_d11b870bf6364341
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M) :
    Exists fun N : SimpleGraph V =>
      M <= N /\ HasPlanarDrawingOn N /\
      (∀ P : SimpleGraph V, N <= P → HasPlanarDrawingOn P → P = N) := by sorry
