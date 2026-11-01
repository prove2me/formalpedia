-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_face_count__p2m_edf71842_1b5c_4584_b66a_8a3d7af33e5d_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_face_count__p2m_edf71842_1b5c_4584_b66a_8a3d7af33e5d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:52:19.340235+00:00
-- url     : https://prove2.me/theorems/6a6f73b1-aafd-4ec3-b910-d68356c6d6db
-- title:
--   Face-count certificate for a maximal planar drawing
-- statement:
--   From a crossing-free drawing and maximality on the fixed vertex set, produce a finite face count satisfying Euler’s equation and the lower bound of three edge incidences per face. The face count is permitted to be zero in the statement, so its boundary cases are not silently excluded; the hypotheses |V| ≥ 3 and maximality are retained. The child removes the conversion from continuous arcs and maximality to the numerical face certificate. A concrete route is to construct a plane embedding, show maximality forces triangular facial boundaries, then count face-edge incidences and use Euler’s formula. The remaining core obligation is this embedding and facial-boundary argument for the exact `HasPlanarDrawingOn` definition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_face_count__p2m_edf71842_1b5c_4584_b66a_8a3d7af33e5d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hmax : ∀ K : SimpleGraph V, G ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = G)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel _
     ∃ f : ℕ,
       Fintype.card V + f = G.edgeFinset.card + 2 ∧
       3 * f ≤ 2 * G.edgeFinset.card) := by sorry
