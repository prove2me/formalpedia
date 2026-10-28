-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_ncard_mono_fd0d87e6_b805_416b_90da_57eb1ca5807e
-- name    : WilliamsonShmoys.edge_ncard_mono_fd0d87e6_b805_416b_90da_57eb1ca5807e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:46:43.322756+00:00
-- url     : https://prove2.me/theorems/38fc62f6-953d-4555-94a3-7756263095e7
-- title:
--   Edge count is monotone under graph inclusion
-- statement:
--   For finite graphs on the same vertex type, inclusion implies monotonicity of the number of edges. Prove this by showing both edge sets are finite, using `hGH` for their set inclusion, and applying finite-set cardinality monotonicity.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_ncard_mono_fd0d87e6_b805_416b_90da_57eb1ca5807e
    {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry
