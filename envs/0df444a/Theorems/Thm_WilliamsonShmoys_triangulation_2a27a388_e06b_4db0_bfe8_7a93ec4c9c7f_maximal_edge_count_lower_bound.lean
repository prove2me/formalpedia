-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_maximal_edge_count_lower_bound
-- name    : WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_maximal_edge_count_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:29:52.699032+00:00
-- url     : https://prove2.me/theorems/2f486b23-4a17-4b27-89f1-8ee712518760
-- title:
--   Maximal planar edge count lower bound
-- statement:
--   An inclusion-maximal graph with the supplied crossing-free drawing and at least three vertices has at least 3|V|−6 edges. The argument is to show that maximality rules out disconnected components and faces with more than three boundary edges, since an additional edge could be drawn inside a face; Euler’s formula and face-edge incidence counting then give the lower bound. The drawing and maximality hypotheses are both needed for this route, and the |V|≥3 boundary is preserved. This separates the augmentation-and-counting argument from the general planar upper bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.triangulation_2a27a388_e06b_4db0_bfe8_7a93ec4c9c7f_maximal_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V <= K.edgeSet.ncard + 6 := by sorry
