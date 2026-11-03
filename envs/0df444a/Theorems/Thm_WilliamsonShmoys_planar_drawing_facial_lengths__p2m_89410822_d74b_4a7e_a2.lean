-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_facial_lengths__p2m_89410822_d74b_4a7e_a2
-- name    : WilliamsonShmoys.planar_drawing_facial_lengths__p2m_89410822_d74b_4a7e_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T22:12:46.807126+00:00
-- url     : https://prove2.me/theorems/bc9cd380-c5b9-4141-b573-8fb0410f4911
-- title:
--   Facial lengths of a connected planar drawing
-- statement:
--   For a finite connected simple graph with at least three vertices and a crossing-free plane drawing, the facial boundary lengths can be indexed by the Euler-predicted number of faces; their sum is twice the edge count and each is at least three. The drawing-to-rotation-system correspondence and the directed-edge face-cycle arguments provide an independent proof route for this part.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_facial_lengths__p2m_89410822_d74b_4a7e_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (length : Fin ((letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 - Fintype.card V) → ℕ),
      2 * (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) =
        ∑ i, length i ∧
      ∀ i, 3 ≤ length i := by sorry
