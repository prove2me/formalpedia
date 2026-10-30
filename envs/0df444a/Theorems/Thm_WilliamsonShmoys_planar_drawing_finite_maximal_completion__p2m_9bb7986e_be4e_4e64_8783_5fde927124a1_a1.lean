-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_finite_maximal_completion__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1
-- name    : WilliamsonShmoys.planar_drawing_finite_maximal_completion__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:46:52.831605+00:00
-- url     : https://prove2.me/theorems/6932dd3a-aa87-467b-ad6b-7c92eed114e6
-- title:
--   Finite maximal planar completion from extension steps
-- statement:
--   If every disconnected drawable supergraph of `G` admits a strict drawable extension, then `G` has a connected drawable supergraph. Choose an inclusion-maximal drawable supergraph from the finite set of graphs on `V`; the extension hypothesis forces it to be connected. Edge-count monotonicity follows from inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_finite_maximal_completion__p2m_9bb7986e_be4e_4e64_8783_5fde927124a1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hStep : ∀ (K : SimpleGraph V), G ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → ¬ K.Connected →
      ∃ K' : SimpleGraph V,
        K ≤ K' ∧ WilliamsonShmoys.HasPlanarDrawingOn K' ∧ K' ≠ K) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
