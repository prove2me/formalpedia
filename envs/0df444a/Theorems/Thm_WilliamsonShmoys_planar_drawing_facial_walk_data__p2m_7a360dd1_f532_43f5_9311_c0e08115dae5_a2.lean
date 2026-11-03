-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_facial_walk_data__p2m_7a360dd1_f532_43f5_9311_c0e08115dae5_a2
-- name    : WilliamsonShmoys.planar_drawing_facial_walk_data__p2m_7a360dd1_f532_43f5_9311_c0e08115dae5_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:42:10.217098+00:00
-- url     : https://prove2.me/theorems/aa3f645f-99ef-419b-ae11-eb7cfec70f83
-- title:
--   Extract facial walk data from a planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a crossing-free drawing has a finite family of facial boundary walks. Every walk has length at least three, each directed edge occurs exactly once across the walks, and Euler’s equation relates the number of vertices, walks, and edges. This isolates the conversion from the given drawing to combinatorial face data. A proof route is to use the drawing as a plane embedding, enumerate its faces and their boundary walks, then establish the incidence and Euler properties. The length condition uses connectedness, simplicity, and the three-vertex lower bound; bridges contribute both directed traversals to a face walk.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_facial_walk_data__p2m_7a360dd1_f532_43f5_9311_c0e08115dae5_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : HasPlanarDrawingOn G) (hConn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    ∃ (k : ℕ) (faces : Fin k → List (V × V)),
      (∀ i, 3 <= (faces i).length) ∧
      (letI : DecidableRel G.Adj := dG; ∀ u v,
        (List.flatten (List.ofFn faces)).count (u, v) =
          if G.Adj u v then 1 else 0) ∧
      Fintype.card V + k =
        (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 2 := by sorry
