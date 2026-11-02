-- Prove2me | Theorems.Thm_simpleGraph_edgeSet_ncard_strictMono__p2m_4a79f535_7c3f_422a_88d6_6cd015f3e78e_a3
-- name    : simpleGraph_edgeSet_ncard_strictMono__p2m_4a79f535_7c3f_422a_88d6_6cd015f3e78e_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:45:46.286793+00:00
-- url     : https://prove2.me/theorems/9d7b609c-431c-4cb9-b3f9-f187a0993d1b
-- title:
--   Proper graph extension increases finite edge-set cardinality
-- statement:
--   For graphs on a finite vertex type, a proper extension has strictly larger edge-set cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem simpleGraph_edgeSet_ncard_strictMono__p2m_4a79f535_7c3f_422a_88d6_6cd015f3e78e_a3 {V : Type} [Fintype V] [LinearOrder V] (G K : SimpleGraph V) (hGK : G ≤ K) (hne : G ≠ K) : G.edgeSet.ncard < K.edgeSet.ncard := by sorry
