-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_b320f89e_6adf_4c95_8da8_b179076388d4_a1
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_b320f89e_6adf_4c95_8da8_b179076388d4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:01:09.773504+00:00
-- url     : https://prove2.me/theorems/a402c68a-d7fd-45a8-9fd3-2080e97d0c7e
-- title:
--   Maximal drawable supergraph on a fixed vertex set
-- statement:
--   Any drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_extension__p2m_b320f89e_6adf_4c95_8da8_b179076388d4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 <= Fintype.card V) :
    exists N : SimpleGraph V,
      M <= N /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      (forall K : SimpleGraph V,
        N <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K <= N) := by sorry
