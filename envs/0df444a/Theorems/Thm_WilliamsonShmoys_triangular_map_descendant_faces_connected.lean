-- Prove2me | Theorems.Thm_WilliamsonShmoys_triangular_map_descendant_faces_connected
-- name    : WilliamsonShmoys.triangular_map_descendant_faces_connected
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T22:17:08.315492+00:00
-- url     : https://prove2.me/theorems/ce39780c-2df3-4580-b1b2-75df35d8b925
-- title:
--   Faces touching a descendant subtree are connected in the complementary dual
-- statement:
--   This is a surface-local connectivity lemma, with no Euler or planarity assumption. Unique root paths identify descendants of v as a subtree. Its contour visits every incident face using duals of chords and half-chords. For a nonroot descendant subtree, the only additional excluded spanning-tree edge is its parent edge. The half-chord duals form closed boundary walks, so removing that parent dual preserves connectivity; this is the mechanism of [Lemma 11](https://arxiv.org/pdf/1306.1595). For the root, the entire complementary dual is connected. For a leaf, the vertex rotation with the parent transition removed supplies connectivity. These cases include the two-faced triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap

theorem WilliamsonShmoys.triangular_map_descendant_faces_connected
    {V F : Type} [Fintype V] [Fintype F]
    {H : SimpleGraph V} (M : WilliamsonShmoys.TriangularMap H F)
    (R : SimpleGraph V) (hRH : R ≤ H) (hR : R.IsTree)
    (root : V) (Q : (v : V) → R.Walk root v)
    (hQ : ∀ v, (Q v).IsPath) (v : V) :
    ((M.cotree R).induce
      {f : F | ∃ i : Fin 3, v ∈ (Q (M.corner f i)).support}).Connected := by sorry
