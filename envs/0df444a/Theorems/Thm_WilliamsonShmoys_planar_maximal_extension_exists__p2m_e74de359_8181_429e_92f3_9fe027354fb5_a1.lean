-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_exists__p2m_e74de359_8181_429e_92f3_9fe027354fb5_a1
-- name    : WilliamsonShmoys.planar_maximal_extension_exists__p2m_e74de359_8181_429e_92f3_9fe027354fb5_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:51:37.803162+00:00
-- url     : https://prove2.me/theorems/7f3e1c59-fb8d-479f-ad2c-408c88d9882e
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every finite drawable simple graph has a drawable supergraph on the same vertices that is inclusion-maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_extension_exists__p2m_e74de359_8181_429e_92f3_9fe027354fb5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    exists K : SimpleGraph V, N <= K /\ HasPlanarDrawingOn K /\
      forall L : SimpleGraph V, K <= L -> HasPlanarDrawingOn L -> L = K := by sorry
