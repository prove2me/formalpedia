-- Prove2me | Theorems.Thm_planar_intermediate_one_edge__p2m_10eaf2f1_7409_4fae_95fa_e1e70a835601_a1
-- name    : planar_intermediate_one_edge__p2m_10eaf2f1_7409_4fae_95fa_e1e70a835601_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:53:28.051431+00:00
-- url     : https://prove2.me/theorems/644ac4c7-7d58-4f76-9e3c-fcf08ce912bf
-- title:
--   One-edge drawable intermediate graph
-- statement:
--   If one drawable graph is a subgraph of another and has strictly fewer edges, there is a drawable intermediate graph containing the first with exactly one additional edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem planar_intermediate_one_edge__p2m_10eaf2f1_7409_4fae_95fa_e1e70a835601_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G M : SimpleGraph V)
    (dG : DecidableRel G.Adj) (dM : DecidableRel M.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hGM : G ≤ M)
    (hlt : G.edgeFinset.card < M.edgeFinset.card) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      G ≤ K ∧
      K.edgeFinset.card = G.edgeFinset.card + 1 := by sorry
