-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_for_triangulated_extension
-- name    : WilliamsonShmoys.exists_maximal_planar_extension_for_triangulated_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:12:51.14174+00:00
-- url     : https://prove2.me/theorems/4b22f485-a3e9-4af2-bd22-a8670c54c50c
-- title:
--   A drawable graph has an inclusion-maximal drawable extension
-- statement:
--   On a finite ordered vertex type, every graph with a planar drawing has a drawable supergraph that is inclusion-maximal among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension_for_triangulated_extension {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn K) : ∃ L : SimpleGraph V, K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L := by sorry
