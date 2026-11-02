-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximalPlanarExtension__p2m_26871514_c4d6_4964_8af5_28b3596c0479_a1
-- name    : WilliamsonShmoys.maximalPlanarExtension__p2m_26871514_c4d6_4964_8af5_28b3596c0479_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:23:14.74641+00:00
-- url     : https://prove2.me/theorems/503a8d71-6799-480d-8f3e-33232e674c95
-- title:
--   Existence of an inclusion-maximal planar extension
-- statement:
--   Every planar graph on the given finite vertex type has a planar supergraph on the same vertices that is maximal under edge inclusion among planar supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximalPlanarExtension__p2m_26871514_c4d6_4964_8af5_28b3596c0479_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : HasPlanarDrawingOn M)
    (hn : 3 ≤ Fintype.card V) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      HasPlanarDrawingOn N ∧
      (letI : DecidableRel M.Adj := dM
       letI : DecidableRel N.Adj := dN
       M.edgeFinset ⊆ N.edgeFinset) ∧
      (∀ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
        HasPlanarDrawingOn K →
        (letI : DecidableRel N.Adj := dN
         letI : DecidableRel K.Adj := dK
         N.edgeFinset ⊆ K.edgeFinset) →
        N = K) := by sorry
