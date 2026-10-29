-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_9b481115_396e_4251_a44a_4293d6576e9f_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9b481115_396e_4251_a44a_4293d6576e9f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T23:29:39.388742+00:00
-- url     : https://prove2.me/theorems/7aca8475-a2b8-409c-a04e-15d75399a1b1
-- title:
--   Every finite drawable graph has a maximal drawable supergraph
-- statement:
--   Any drawable graph on a finite ordered vertex type is contained in a drawable supergraph that has no strictly larger drawable supergraph on those same vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9b481115_396e_4251_a44a_4293d6576e9f_a1 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N) : ∃ M : SimpleGraph V, N ≤ M ∧ WilliamsonShmoys.HasPlanarDrawingOn M ∧ ∀ K : SimpleGraph V, M ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = M := by sorry
