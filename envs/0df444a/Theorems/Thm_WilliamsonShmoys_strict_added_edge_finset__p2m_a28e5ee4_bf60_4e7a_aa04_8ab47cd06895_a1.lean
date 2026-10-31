-- Prove2me | Theorems.Thm_WilliamsonShmoys_strict_added_edge_finset__p2m_a28e5ee4_bf60_4e7a_aa04_8ab47cd06895_a1
-- name    : WilliamsonShmoys.strict_added_edge_finset__p2m_a28e5ee4_bf60_4e7a_aa04_8ab47cd06895_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T06:15:31.962718+00:00
-- url     : https://prove2.me/theorems/4be3bdb9-1c14-44bd-883e-1f23fe5aa48f
-- title:
--   Strict edge-finset growth for an added nonedge
-- statement:
--   If `L` has exactly the edges of `K` together with the unordered pair `{u,v}`, and `u` and `v` are not adjacent in `K`, then `K`’s edge finset is a strict subset of `L`’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.strict_added_edge_finset__p2m_a28e5ee4_bf60_4e7a_aa04_8ab47cd06895_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V) [DecidableRel K.Adj] [DecidableRel L.Adj]
    (u v : V) (huv : u < v) (hnonadj : ¬ K.Adj u v)
    (hLrel : ∀ a b, L.Adj a b ↔
      K.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) :
    K.edgeFinset ⊂ L.edgeFinset := by sorry
