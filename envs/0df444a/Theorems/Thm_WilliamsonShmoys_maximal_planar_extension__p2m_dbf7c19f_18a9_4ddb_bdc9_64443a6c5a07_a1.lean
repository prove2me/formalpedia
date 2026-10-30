-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_dbf7c19f_18a9_4ddb_bdc9_64443a6c5a07_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_dbf7c19f_18a9_4ddb_bdc9_64443a6c5a07_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:18:58.505807+00:00
-- url     : https://prove2.me/theorems/e2660803-7fa4-4904-92ad-33d688ae9d12
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertex type that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension__p2m_dbf7c19f_18a9_4ddb_bdc9_64443a6c5a07_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, LE.le K L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, LE.le L M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
