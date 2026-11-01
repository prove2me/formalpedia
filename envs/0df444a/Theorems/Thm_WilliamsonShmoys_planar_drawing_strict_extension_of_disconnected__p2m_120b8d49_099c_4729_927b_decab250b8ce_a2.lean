-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_strict_extension_of_disconnected__p2m_120b8d49_099c_4729_927b_decab250b8ce_a2
-- name    : WilliamsonShmoys.planar_drawing_strict_extension_of_disconnected__p2m_120b8d49_099c_4729_927b_decab250b8ce_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T22:11:44.731237+00:00
-- url     : https://prove2.me/theorems/8b80d452-fe2a-4452-803d-c92a5938bb15
-- title:
--   A disconnected planar drawing admits a strict planar extension
-- statement:
--   If a finite ordered vertex graph has a crossing-free drawing and is disconnected, it has a strictly larger planar supergraph on the same vertices. This step removes the obligation to prove connectivity in one move; it isolates the geometric edge-augmentation argument. A proof route is to work in the given embedding, choose distinct components, and draw an arc through a face joining them while verifying the predicate's vertex-avoidance and pairwise-intersection conditions. The child applies whenever the graph is disconnected, so its boundary case already supplies at least two vertices; it needs no separate cardinality bound. The unresolved work is the formal face/arc construction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_strict_extension_of_disconnected__p2m_120b8d49_099c_4729_927b_decab250b8ce_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hDisconnected : ¬ H.Connected) :
    ∃ K : SimpleGraph V, H < K ∧ HasPlanarDrawingOn K := by
  sorry
