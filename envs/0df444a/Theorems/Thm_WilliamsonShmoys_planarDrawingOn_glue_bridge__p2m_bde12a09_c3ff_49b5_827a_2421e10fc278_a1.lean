-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_glue_bridge__p2m_bde12a09_c3ff_49b5_827a_2421e10fc278_a1
-- name    : WilliamsonShmoys.planarDrawingOn_glue_bridge__p2m_bde12a09_c3ff_49b5_827a_2421e10fc278_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:44:30.826209+00:00
-- url     : https://prove2.me/theorems/0b563259-ebc2-4b95-bb4e-e52d7b772925
-- title:
--   Glue disjointly supported planar drawings with a bridge
-- statement:
--   If two planar graphs have all their edge endpoints on opposite sides of a vertex partition, construct a planar drawing of their union with exactly the bridge edge uv added.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_glue_bridge__p2m_bde12a09_c3ff_49b5_827a_2421e10fc278_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (A B : SimpleGraph V) (S : Set V) (u v : V)
    (hA : HasPlanarDrawingOn A) (hB : HasPlanarDrawingOn B)
    (hAs : ∀ a b, A.Adj a b → a ∈ S ∧ b ∈ S)
    (hBs : ∀ a b, B.Adj a b → a ∉ S ∧ b ∉ S)
    (hu : u ∈ S) (hv : v ∉ S) :
    ∃ H : SimpleGraph V,
      HasPlanarDrawingOn H ∧
      (∀ a b, H.Adj a b ↔
        A.Adj a b ∨ B.Adj a b ∨
          (a = u ∧ b = v) ∨ (a = v ∧ b = u)) := by sorry
