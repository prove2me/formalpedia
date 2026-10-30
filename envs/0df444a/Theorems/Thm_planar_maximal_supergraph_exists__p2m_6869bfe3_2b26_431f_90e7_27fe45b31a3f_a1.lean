-- Prove2me | Theorems.Thm_planar_maximal_supergraph_exists__p2m_6869bfe3_2b26_431f_90e7_27fe45b31a3f_a1
-- name    : planar_maximal_supergraph_exists__p2m_6869bfe3_2b26_431f_90e7_27fe45b31a3f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:14:44.140893+00:00
-- url     : https://prove2.me/theorems/7fd45cf3-e203-47de-9dbd-2f0909dacdf1
-- title:
--   A drawable graph has a maximal drawable supergraph
-- statement:
--   Every finite drawable graph on at least three vertices is contained in a drawable supergraph maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem planar_maximal_supergraph_exists__p2m_6869bfe3_2b26_431f_90e7_27fe45b31a3f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hV : LE.le 3 (Fintype.card V)) :
    ∃ M : SimpleGraph V,
      LE.le L M ∧ HasPlanarDrawingOn M ∧
        ∀ N : SimpleGraph V, HasPlanarDrawingOn N → LE.le M N → LE.le N M := by
  sorry
