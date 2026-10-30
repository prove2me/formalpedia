-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edgeFinset_card_ge_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1
-- name    : WilliamsonShmoys.maximal_drawable_edgeFinset_card_ge_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:13.818019+00:00
-- url     : https://prove2.me/theorems/b8ffaa04-868a-495a-ab39-10d09a3d9b95
-- title:
--   Maximal drawable graph edge-count lower bound
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has at least 3n−6 edges. This isolates the part that uses maximality. A proof route is to pass from the given drawing to its plane embedding, show each face boundary is triangular (otherwise a nonedge diagonal can be added inside a face, creating a drawable strict supergraph), and combine the resulting face-edge count with Euler's formula. The boundary assumption is retained to keep the edge-count arithmetic valid.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edgeFinset_card_ge_three_mul_card_sub_six__p2m_16e02065_aa02_4917_a9e7_1c4778a9d41f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) [DecidableRel M.Adj]
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, M ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeFinset.card := by sorry
