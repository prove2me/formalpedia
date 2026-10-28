-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_connected_supergraph
-- name    : WilliamsonShmoys.planarDrawing_connected_supergraph
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T11:31:14.276108+00:00
-- url     : https://prove2.me/theorems/aeda4c22-ea60-4d70-adf4-5224e0d2ce33
-- title:
--   Connected planar supergraph extension
-- statement:
--   Every finite graph with at least three vertices and a supplied crossing-free drawing has a connected planar supergraph on the same vertices. The lemma isolates the geometric augmentation from the target’s edge-count conclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_connected_supergraph
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v : V⦄, G.Adj u v → H.Adj u v) ∧
      H.Connected ∧ HasPlanarDrawingOn H := by sorry
