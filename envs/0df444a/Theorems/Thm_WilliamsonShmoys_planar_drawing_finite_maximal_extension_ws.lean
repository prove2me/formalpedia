-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_extension_ws
-- name    : WilliamsonShmoys.planar_drawing_finite_maximal_extension_ws
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:11:37.353585+00:00
-- url     : https://prove2.me/theorems/9c240a5a-99cd-4fd1-a863-632c361ff265
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph that is maximal among drawable supergraphs on that same vertex type. Choose a drawable supergraph with the largest edge count; finiteness of the possible simple graphs supplies the maximum.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_finite_maximal_extension_ws {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by sorry
