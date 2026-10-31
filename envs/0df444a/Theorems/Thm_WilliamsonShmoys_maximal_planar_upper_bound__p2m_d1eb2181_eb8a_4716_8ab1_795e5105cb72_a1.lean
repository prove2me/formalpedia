-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_upper_bound__p2m_d1eb2181_eb8a_4716_8ab1_795e5105cb72_a1
-- name    : WilliamsonShmoys.maximal_planar_upper_bound__p2m_d1eb2181_eb8a_4716_8ab1_795e5105cb72_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:38:34.714546+00:00
-- url     : https://prove2.me/theorems/2e520467-0d96-4c71-b340-b60069871ecd
-- title:
--   Planar graph edge upper bound
-- statement:
--   A finite simple graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This is the planar Euler bound; the strict vertex threshold is preserved.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_upper_bound__p2m_d1eb2181_eb8a_4716_8ab1_795e5105cb72_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) (hV : 3 <= Fintype.card V) : H.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
