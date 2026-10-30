-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_91c62409_832a_420e_9e29_0b556e5e78fe_a1
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_91c62409_832a_420e_9e29_0b556e5e78fe_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:09:40.713712+00:00
-- url     : https://prove2.me/theorems/b466455e-5718-4066-9460-9ed1b12c8d5e
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex set has a maximal drawable supergraph on that same vertex set. The proof route orders drawable supergraphs by inclusion and chooses a maximal member from the finite collection of simple graphs on `V`; the vertex-count hypothesis is preserved for the subsequent edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension__p2m_91c62409_832a_420e_9e29_0b556e5e78fe_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) : ∃ U : SimpleGraph V, T ≤ U ∧ WilliamsonShmoys.HasPlanarDrawingOn U ∧ ∀ W : SimpleGraph V, U ≤ W → WilliamsonShmoys.HasPlanarDrawingOn W → W = U := by sorry
