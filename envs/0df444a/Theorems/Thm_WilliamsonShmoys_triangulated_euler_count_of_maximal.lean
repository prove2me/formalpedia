-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulated_euler_count_of_maximal
-- name    : WilliamsonShmoys.triangulated_euler_count_of_maximal
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T05:09:22.217752+00:00
-- url     : https://prove2.me/theorems/def6ae5e-bde9-4d7e-98ba-cdd8403c7813
-- title:
--   Maximal drawable graphs admit Euler and triangular-face counts
-- statement:
--   For a drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertices, there is a natural face count satisfying Euler's equation and the triangular-face incidence equation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.triangulated_euler_count_of_maximal
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    ∃ f : ℕ,
      Fintype.card V + f = K.edgeSet.ncard + 2 ∧
      3 * f = 2 * K.edgeSet.ncard := by sorry
