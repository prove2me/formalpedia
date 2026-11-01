-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_extension__p2m_fcfb21bb_7adb_48c4_98c9_78175b7ac091_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph_extension__p2m_fcfb21bb_7adb_48c4_98c9_78175b7ac091_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:08.70777+00:00
-- url     : https://prove2.me/theorems/4af6ea92-4c22-435e-a0b4-a6c72b25ac6d
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph_extension__p2m_fcfb21bb_7adb_48c4_98c9_78175b7ac091_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    Exists fun N : SimpleGraph V =>
      (forall {u v : V}, M.Adj u v -> N.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      (forall P : SimpleGraph V,
        (forall {u v : V}, N.Adj u v -> P.Adj u v) ->
        WilliamsonShmoys.HasPlanarDrawingOn P -> P = N) := by sorry
