-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T08:13:51.892044+00:00
-- url     : https://prove2.me/theorems/9cbf7930-27f5-4ec1-bd84-90973878ef98
-- title:
--   Maximal planar supergraph extension
-- statement:
--   A graph with a planar drawing on a finite vertex set has a planar supergraph on that same vertex set that is maximal among planar supergraphs. The proof route is finite maximization by edge count; the size hypothesis is retained for compatibility with the target and covers the triangle boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal_extension {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : WilliamsonShmoys.HasPlanarDrawingOn L) : ∃ H : SimpleGraph V, L ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ (∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) := by sorry
