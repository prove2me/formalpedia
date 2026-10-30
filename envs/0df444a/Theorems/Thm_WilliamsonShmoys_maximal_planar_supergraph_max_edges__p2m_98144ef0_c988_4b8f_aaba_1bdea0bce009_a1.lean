-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_max_edges__p2m_98144ef0_c988_4b8f_aaba_1bdea0bce009_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_max_edges__p2m_98144ef0_c988_4b8f_aaba_1bdea0bce009_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:26:24.544817+00:00
-- url     : https://prove2.me/theorems/7c956806-2ea1-472c-9837-05b1b852605b
-- title:
--   A maximum-edge planar supergraph exists
-- statement:
--   Among the planar supergraphs of K on the same finite vertex type, one has at least as many edges as every other planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph_max_edges__p2m_98144ef0_c988_4b8f_aaba_1bdea0bce009_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, K ≤ M → HasPlanarDrawingOn M →
        Nat.card {e : Sym2 V // e ∈ M.edgeSet} ≤
          Nat.card {e : Sym2 V // e ∈ L.edgeSet}) := by sorry
