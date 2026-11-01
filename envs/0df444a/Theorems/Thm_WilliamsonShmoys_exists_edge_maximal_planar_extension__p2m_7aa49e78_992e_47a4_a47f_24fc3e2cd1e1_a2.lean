-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension__p2m_7aa49e78_992e_47a4_a47f_24fc3e2cd1e1_a2
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_7aa49e78_992e_47a4_a47f_24fc3e2cd1e1_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:33:55.120159+00:00
-- url     : https://prove2.me/theorems/adc3d123-0e13-438c-852d-da6c76884acd
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every connected drawable graph on a finite vertex type has a drawable supergraph that is maximal under edge inclusion among drawable graphs on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_extension__p2m_7aa49e78_992e_47a4_a47f_24fc3e2cd1e1_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hconn : K.Connected)
    (hK : HasPlanarDrawingOn K) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ G : SimpleGraph V,
      K.edgeFinset ⊆ G.edgeFinset ∧
      HasPlanarDrawingOn G ∧
      ∀ H : SimpleGraph V,
        G.edgeFinset ⊆ H.edgeFinset →
        HasPlanarDrawingOn H →
        H.edgeFinset ⊆ G.edgeFinset := by
  sorry
