-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension__p2m_18964b7c_c181_43c8_b19b_00116e3fbbcb_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_extension__p2m_18964b7c_c181_43c8_b19b_00116e3fbbcb_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T11:54:13.891394+00:00
-- url     : https://prove2.me/theorems/988c1904-dc70-4d15-915a-a0c8e2ace48d
-- title:
--   Choose an inclusion-maximal drawable supergraph
-- statement:
--   Every drawable finite graph has a drawable supergraph on the same vertex set that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_extension__p2m_18964b7c_c181_43c8_b19b_00116e3fbbcb_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      H.edgeFinset ⊆ K.edgeFinset ∧
      HasPlanarDrawingOn K ∧
      (∀ (L : SimpleGraph V) [DecidableRel L.Adj],
        (∀ {u v}, K.Adj u v → L.Adj u v) →
        HasPlanarDrawingOn L →
        ∀ {u v}, L.Adj u v → K.Adj u v) := by sorry
