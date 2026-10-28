-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_exists_maximal_f1f92bb7
-- name    : WilliamsonShmoys.planar_supergraph_exists_maximal_f1f92bb7
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T06:18:29.06772+00:00
-- url     : https://prove2.me/theorems/d2c227e3-a33e-41bd-8e36-94cb45b21f60
-- title:
--   A finite planar graph has an edge-maximal planar extension
-- statement:
--   Every finite graph with a crossing-free drawing has an edge-maximal crossing-free supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_exists_maximal_f1f92bb7 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
