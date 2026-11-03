-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_54b85171_3c84_49d0_b75e_a1ac45808ba4_a2
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_54b85171_3c84_49d0_b75e_a1ac45808ba4_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:36:44.583515+00:00
-- url     : https://prove2.me/theorems/c8598e77-6e42-4024-86ce-049edcd78b20
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   A planar graph on a finite ordered vertex type has an inclusion-maximal planar supergraph on that same vertex type. This removes the augmentation step from the parent. A proof route is to maximize edge count among the finitely many simple graphs containing M and having a planar drawing; the key fact is that any strict supergraph has more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_54b85171_3c84_49d0_b75e_a1ac45808ba4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn N ∧ M ≤ N ∧
      ∀ K : SimpleGraph V,
        WilliamsonShmoys.HasPlanarDrawingOn K → N ≤ K → K = N := by
  sorry
