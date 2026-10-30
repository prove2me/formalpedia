-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_exists__p2m_706d02aa_87d3_4c47_be20_96ce2bbf8d05_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_706d02aa_87d3_4c47_be20_96ce2bbf8d05_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:09:23.310886+00:00
-- url     : https://prove2.me/theorems/441d46dd-32c1-48a0-83ae-f4dcdc7108f6
-- title:
--   Extend a drawn graph to a maximal planar supergraph
-- statement:
--   Every graph with the supplied crossing-free drawing is contained, on the same vertex set, in a maximal simple graph that also has such a drawing. The finite set of possible edges gives a concrete route: add admissible edges while preserving a drawing until no further edge can be added. The `|V| ≥ 3` assumption is preserved for the edge-count step; isolated vertices and disconnected components must be handled during the drawing extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph_exists__p2m_706d02aa_87d3_4c47_be20_96ce2bbf8d05_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
