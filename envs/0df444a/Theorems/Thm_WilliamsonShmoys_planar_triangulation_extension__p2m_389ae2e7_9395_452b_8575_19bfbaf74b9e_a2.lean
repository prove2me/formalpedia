-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_389ae2e7_9395_452b_8575_19bfbaf74b9e_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_389ae2e7_9395_452b_8575_19bfbaf74b9e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:32:37.328977+00:00
-- url     : https://prove2.me/theorems/2a02a607-0135-4f55-809a-3285938451f0
-- title:
--   Drawable triangulation extension with exact edge count
-- statement:
--   Every drawable finite simple graph on at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. This removes the augmentation and Euler-count argument from the parent; an independent route is to extend the embedding to a maximal planar graph, prove its faces are triangular, and count vertices, edges, and faces with Euler’s formula. The remaining core obligation is establishing that extension theorem rigorously for the given drawing predicate, including disconnected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_389ae2e7_9395_452b_8575_19bfbaf74b9e_a2 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hCard : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧ L.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
