-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_20afdcd4_5dba_470f_a57a_287711f6e0ce_a2
-- name    : WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_20afdcd4_5dba_470f_a57a_287711f6e0ce_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:13:22.131989+00:00
-- url     : https://prove2.me/theorems/afcb74a2-92ae-4444-9657-28f7f6cf41f5
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph maximal among its drawable supergraphs on that vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_20afdcd4_5dba_470f_a57a_287711f6e0ce_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    Exists fun M : SimpleGraph V =>
      WilliamsonShmoys.HasPlanarDrawingOn M /\ L <= M /\
        (forall N : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn N -> M <= N -> N = M) := by sorry
