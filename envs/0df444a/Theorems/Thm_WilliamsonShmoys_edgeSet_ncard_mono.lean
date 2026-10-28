-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono
-- name    : WilliamsonShmoys.edgeSet_ncard_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:27:48.334336+00:00
-- url     : https://prove2.me/theorems/74593c2a-18da-4ed9-b445-c05cc3206216
-- title:
--   Monotonicity of finite graph edge counts
-- statement:
--   If one finite graph is a subgraph of another on the same vertex type, its edge-set cardinality is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
