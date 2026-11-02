-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:05:29.141495+00:00
-- url     : https://prove2.me/theorems/04c04e16-b235-4c68-889f-e3b37d35b24b
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every finite drawable graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (_ : DecidableRel K.Adj),
      (∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ (L : SimpleGraph V),
        (∀ u v, K.Adj u v → L.Adj u v) →
        WilliamsonShmoys.HasPlanarDrawingOn L →
        ∀ u v, L.Adj u v → K.Adj u v) := by sorry
