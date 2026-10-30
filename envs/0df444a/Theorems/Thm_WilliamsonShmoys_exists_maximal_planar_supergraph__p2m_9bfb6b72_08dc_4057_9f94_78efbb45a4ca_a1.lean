-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_9bfb6b72_08dc_4057_9f94_78efbb45a4ca_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9bfb6b72_08dc_4057_9f94_78efbb45a4ca_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:59:01.748122+00:00
-- url     : https://prove2.me/theorems/1d8ac9c8-ae9e-4d86-8ce6-dc2f073f2eeb
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every drawable finite simple graph is contained in a drawable graph on the same vertices that has no strictly larger drawable supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_9bfb6b72_08dc_4057_9f94_78efbb45a4ca_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ H' : SimpleGraph V, H ≤ H' → HasPlanarDrawingOn H' → H' = H := by
  sorry
