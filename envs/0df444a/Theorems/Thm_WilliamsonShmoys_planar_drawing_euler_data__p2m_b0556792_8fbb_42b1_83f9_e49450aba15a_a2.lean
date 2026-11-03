-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_euler_data__p2m_b0556792_8fbb_42b1_83f9_e49450aba15a_a2
-- name    : WilliamsonShmoys.planar_drawing_euler_data__p2m_b0556792_8fbb_42b1_83f9_e49450aba15a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:27:12.52965+00:00
-- url     : https://prove2.me/theorems/c4d77529-9abd-4bdb-a9e4-27423a3195e5
-- title:
--   Euler and face data from a planar drawing
-- statement:
--   Given the stated crossing-free drawing on at least three vertices, extend it to a connected planar supergraph K on the same vertices and obtain its Euler face count f and total facial boundary length l. The outputs assert that K contains H, its edge count dominates H's, Euler's equation holds, each edge contributes two face sides, and every facial boundary has length at least three in total. A proof route is to regard the finite family of simple arcs as a plane embedding, add noncrossing edges until the embedding is maximal on the fixed vertex set, and count the facial boundary walks; maximality gives triangular faces, including the three-vertex boundary case. This is the substantive remaining topological obligation; the parent uses only the edge-count monotonicity and numerical data.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_euler_data__p2m_b0556792_8fbb_42b1_83f9_e49450aba15a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     ∃ K : SimpleGraph V, H ≤ K ∧
       (letI : DecidableRel K.Adj := Classical.decRel K.Adj
        H.edgeFinset.card ≤ K.edgeFinset.card ∧
        ∃ f l : ℕ,
          Fintype.card V + f = K.edgeFinset.card + 2 ∧
          l = 2 * K.edgeFinset.card ∧
          3 * f ≤ l)) := by sorry
