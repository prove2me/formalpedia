-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_supergraph_finite_maximal_extension
-- name    : WilliamsonShmoys.exists_planar_supergraph_finite_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:18:18.23492+00:00
-- url     : https://prove2.me/theorems/f60d9400-76e4-4343-a9c9-47b7bf7efc6a
-- title:
--   A finite planar supergraph extension is maximal
-- statement:
--   Every drawable finite graph on the given vertex type has a supergraph maximal under inclusion among drawable graphs on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_supergraph_finite_maximal_extension {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) (hcard : 3 ≤ Fintype.card V) : ∃ K : SimpleGraph V, G ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
