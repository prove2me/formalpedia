-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a2
-- name    : WilliamsonShmoys.planar_drawing_augmentation__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:47:56.774292+00:00
-- url     : https://prove2.me/theorems/bee93123-d53b-4163-8710-18b1a42ddf7b
-- title:
--   Augment a planar drawing to a maximal planar supergraph
-- statement:
--   A finite graph with a planar drawing is contained in an inclusion-maximal planar supergraph on the same vertices, with at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_augmentation__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hdrawing : HasPlanarDrawingOn G) :
    (letI : ∀ K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj;
      ∃ H : SimpleGraph V,
        G ≤ H ∧ HasPlanarDrawingOn H ∧
          (∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) ∧
          G.edgeFinset.card ≤ H.edgeFinset.card) := by sorry
