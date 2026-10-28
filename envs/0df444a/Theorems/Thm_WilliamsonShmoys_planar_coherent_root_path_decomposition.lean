-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_coherent_root_path_decomposition
-- name    : WilliamsonShmoys.planar_coherent_root_path_decomposition
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T21:44:27.575411+00:00
-- url     : https://prove2.me/theorems/05b45820-d0ea-449c-890f-ee4a6fac462f
-- title:
--   Planar tree–cotree decomposition covered by three prescribed root paths
-- statement:
--   For any coherent simple root-path system in a graph with the packaged planar drawing, the root component has a finite tree decomposition whose bags are covered by three prescribed root paths. No shortestness or annulus hypothesis is required. Use the paths’ spanning tree, a triangulated planar completion retaining it, and the complementary dual tree; face bags give the required cover and connected occurrence sets. Handle components of size one or two with one bag. This isolates the geometric construction from BFS selection and quantitative counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

theorem WilliamsonShmoys.planar_coherent_root_path_decomposition
    {n : Nat} (G : SimpleGraph (Fin n)) (root : Fin n)
    (hG : WilliamsonShmoys.HasPlanarDrawing G)
    (P : (v : {x : Fin n // G.Reachable root x}) → G.Walk root v.val)
    (hpath : ∀ v, (P v).IsPath)
    (hprefix : ∀ u v : {x : Fin n // G.Reachable root x},
      u.val ∈ (P v).support → (P u).IsSubwalk (P v)) :
    ∃ (T : Type) (_ : Fintype T) (t : SimpleGraph T)
      (X : T → Finset {x : Fin n // G.Reachable root x}),
      RobertsonSeymour1986.GM5.IsTreeDecomposition
        (G.induce {x : Fin n | G.Reachable root x}) t X ∧
      ∀ s, ∃ a b c : {x : Fin n // G.Reachable root x},
        ∀ v ∈ X s,
          v.val ∈ (P a).support ∨
          v.val ∈ (P b).support ∨
          v.val ∈ (P c).support := by sorry
