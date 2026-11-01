-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_92fbdf79_5590_491f_9884_21ba60b9e74f_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_92fbdf79_5590_491f_9884_21ba60b9e74f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:13:33.948304+00:00
-- url     : https://prove2.me/theorems/2178e3b5-32a6-46a2-b66f-ec00b9247342
-- title:
--   Finite maximal drawable supergraph exists
-- statement:
--   Every drawable simple graph on a finite ordered vertex type is contained in a drawable supergraph that has no strictly larger drawable supergraph on that same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open scoped BigOperators

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_92fbdf79_5590_491f_9884_21ba60b9e74f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
