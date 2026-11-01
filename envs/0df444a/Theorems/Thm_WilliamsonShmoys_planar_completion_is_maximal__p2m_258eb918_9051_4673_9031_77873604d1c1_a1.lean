-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_completion_is_maximal__p2m_258eb918_9051_4673_9031_77873604d1c1_a1
-- name    : WilliamsonShmoys.planar_completion_is_maximal__p2m_258eb918_9051_4673_9031_77873604d1c1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:45:21.585578+00:00
-- url     : https://prove2.me/theorems/f914dab2-91be-415e-a370-d761f8bbdaba
-- title:
--   Planar completion to an inclusion-maximal supergraph
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex type that admits no strict drawable supergraph on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_completion_is_maximal__p2m_258eb918_9051_4673_9031_77873604d1c1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H := by sorry
