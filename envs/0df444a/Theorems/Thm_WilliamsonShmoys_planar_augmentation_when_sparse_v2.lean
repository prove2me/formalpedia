-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_augmentation_when_sparse_v2
-- name    : WilliamsonShmoys.planar_augmentation_when_sparse_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:46:26.949259+00:00
-- url     : https://prove2.me/theorems/729fc1e5-7595-4c6b-88b7-16892de5217a
-- title:
--   Strict planar extension for a sparse drawing
-- statement:
--   A planar graph on at least three vertices with fewer than 3|V|−6 edges has a strict planar supergraph on the same vertex set. The strict inequality is needed to ensure a genuinely new edge can be added.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_augmentation_when_sparse_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hsparse : Q.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ R : SimpleGraph V, Q ≤ R ∧ R ≠ Q ∧
      WilliamsonShmoys.HasPlanarDrawingOn R := by sorry
