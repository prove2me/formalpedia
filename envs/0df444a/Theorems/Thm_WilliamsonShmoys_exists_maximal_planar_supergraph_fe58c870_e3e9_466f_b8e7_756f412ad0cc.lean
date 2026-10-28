-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_fe58c870_e3e9_466f_b8e7_756f412ad0cc
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_fe58c870_e3e9_466f_b8e7_756f412ad0cc
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:28:45.15286+00:00
-- url     : https://prove2.me/theorems/4a509aa3-ce98-452c-99ba-8f71f7ff55e9
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   Every finite graph admitting the supplied crossing-free drawing has a supergraph on the same vertices that admits such a drawing and is maximal under graph inclusion. Choose a planar supergraph with the largest edge count; any strict planar supergraph would add an edge and contradict maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_fe58c870_e3e9_466f_b8e7_756f412ad0cc
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
