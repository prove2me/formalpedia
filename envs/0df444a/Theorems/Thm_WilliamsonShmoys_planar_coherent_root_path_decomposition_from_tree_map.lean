-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_coherent_root_path_decomposition_from_tree_map
-- name    : WilliamsonShmoys.planar_coherent_root_path_decomposition_from_tree_map
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T22:27:24.708881+00:00
-- url     : https://prove2.me/theorems/6b1273d4-0197-4e71-a25f-6a287160d808
-- title:
--   Build the three-path decomposition from a rooted tree and triangular map
-- statement:
--   Assign each triangular-map face a bag consisting of the vertices on the three rooted tree paths to its corners. Corner coverage gives vertex coverage, dart coverage gives edge coverage, and the bag definition gives the three-path cover. The assumed connectedness of the incident-face sets gives the running-intersection condition because the complementary dual is a tree. In the planar specialization of Dujmović–Morin–Wood, Theorem 12, this isolates the face-bag construction from the geometric and dual-connectivity obligations. The boundary hypotheses explicitly require a finite reachable subtype, a tree of root paths, a complementary dual tree, and connected incident-face sets.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_RobertsonSeymour1986_GM5_IsTreeDecomposition
import Definitions.Def_WilliamsonShmoys_TriangularMap
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Combinatorics.SimpleGraph.Walk.Subwalks

theorem WilliamsonShmoys.planar_coherent_root_path_decomposition_from_tree_map
    {n : Nat} (G : SimpleGraph (Fin n)) (root : Fin n)
    [Fintype {x : Fin n // G.Reachable root x}]
    (R : SimpleGraph {x : Fin n // G.Reachable root x})
    (hRG : R ≤ G.induce {x : Fin n | G.Reachable root x})
    (hR : R.IsTree)
    (Q : (v : {x : Fin n // G.Reachable root x}) →
      R.Walk ⟨root, SimpleGraph.Reachable.refl root⟩ v)
    (hQ : ∀ v, (Q v).IsPath)
    (H : SimpleGraph {x : Fin n // G.Reachable root x})
    (hGH : G.induce {x : Fin n | G.Reachable root x} ≤ H)
    (m : Nat) (M : WilliamsonShmoys.TriangularMap H (Fin m))
    (hRH : R ≤ H)
    (hD : (M.cotree R).IsTree)
    (hFace : ∀ v : {x : Fin n // G.Reachable root x},
      ((M.cotree R).induce
        {f : Fin m | ∃ i : Fin 3, v ∈ (Q (M.corner f i)).support}).Connected) :
    ∃ (T : Type) (_ : Fintype T) (t : SimpleGraph T)
      (X : T → Finset {x : Fin n // G.Reachable root x}),
      RobertsonSeymour1986.GM5.IsTreeDecomposition
        (G.induce {x : Fin n | G.Reachable root x}) t X ∧
      ∀ s, ∃ a b c : {x : Fin n // G.Reachable root x},
        ∀ v ∈ X s,
          v ∈ (Q a).support ∨ v ∈ (Q b).support ∨ v ∈ (Q c).support := by sorry
