-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
-- name    : WilliamsonShmoys.planar_extension_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:47:40.56391+00:00
-- url     : https://prove2.me/theorems/c7554adc-1233-4cba-a9cd-d064acd0eee7
-- title:
--   Extend a planar drawing to a sharp edge-count supergraph
-- statement:
--   Extend the given crossing-free drawing to a supergraph on the same vertices with exactly 3n−6 edges. This removes the drawing and Euler argument from the parent. A proof route is to connect components using noncrossing arcs, continue adding noncrossing edges until the embedding is maximal, show maximality forces triangular faces, and apply Euler’s formula. The n≥3 hypothesis handles the sharp boundary case: for n=3 the extension is a triangle. The remaining core obligation is to formalize this augmentation and face-count argument from the continuous-arc drawing definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_extension_4881293e_7bf5_4184_9f0b_57a8f75b0b6d
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 <= Fintype.card V) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧ T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
