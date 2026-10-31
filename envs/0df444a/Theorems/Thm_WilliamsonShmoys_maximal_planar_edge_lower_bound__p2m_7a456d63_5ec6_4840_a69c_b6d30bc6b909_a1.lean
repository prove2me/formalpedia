-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:22:28.332981+00:00
-- url     : https://prove2.me/theorems/f6ef00c3-9a62-41aa-bbc8-b32342398c0c
-- title:
--   Maximal drawable graphs meet the triangulation edge threshold
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable simple graph on the same vertex type has at least `3|V|−6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hLplanar : WilliamsonShmoys.HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) (hLmax : ∀ M : SimpleGraph V, LE.le L M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L) : 3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
