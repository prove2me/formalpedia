-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_af8ffdb6_a3ca_4deb_99d5_c1621ba2f570_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_extension__p2m_af8ffdb6_a3ca_4deb_99d5_c1621ba2f570_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:35:36.689858+00:00
-- url     : https://prove2.me/theorems/ab37673e-752a-4f25-b370-896a68a34722
-- title:
--   Existence of a maximal drawable extension
-- statement:
--   Every drawable graph on a finite vertex set has an inclusion-maximal drawable supergraph on that same vertex set. This follows by maximizing edge count over the finite collection of drawable supergraphs; the stated cardinality hypothesis is retained for direct use alongside the edge-count lemma.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_extension__p2m_af8ffdb6_a3ca_4deb_99d5_c1621ba2f570_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M := by sorry
