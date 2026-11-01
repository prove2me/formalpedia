-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:47:14.687677+00:00
-- url     : https://prove2.me/theorems/168460db-bad2-471e-a83e-74dae3ce8af4
-- title:
--   Maximal drawable extension
-- statement:
--   Every drawable graph on the finite vertex set has a drawable supergraph on that same set that is maximal under edge inclusion. This follows by choosing a drawable supergraph with the largest number of edges; there are only finitely many simple graphs on the vertex set. It removes the extension-existence step from the parent. The geometric drawing can be kept unchanged when considering each candidate supergraph, while the key remaining work for this child is formalizing finite maximal choice with the graph order and drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_98d2ce50_16ca_4db3_bebc_b1953e5d6a1b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T) :
    ∃ U : SimpleGraph V,
      T ≤ U ∧ HasPlanarDrawingOn U ∧
        ∀ W : SimpleGraph V, U ≤ W → HasPlanarDrawingOn W → W = U := by sorry
