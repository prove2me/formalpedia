-- Prove2me | Theorems.Thm_WilliamsonShmoys_efb0a43e_maximal_drawable_exact_edge_count
-- name    : WilliamsonShmoys.efb0a43e_maximal_drawable_exact_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T23:47:45.56359+00:00
-- url     : https://prove2.me/theorems/51cf6003-2dc3-4ddc-ba40-9d49bf38afc4
-- title:
--   Maximal drawable graphs have the planar edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.efb0a43e_maximal_drawable_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L = K) :
    K.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
