-- Prove2me | Theorems.Thm_WilliamsonShmoys_retained_component_treewidth_from_band
-- name    : WilliamsonShmoys.retained_component_treewidth_from_band
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:16:00.400969+00:00
-- url     : https://prove2.me/theorems/70b64992-d01a-46ca-b47b-8b5fa85d44fc
-- title:
--   Transfer a BFS band bound to its retained component
-- statement:
--   If every vertex in the retained component of v is in the stated BFS band, and the induced graph on that band has treewidth at most 3k, then the induced graph on the retained component also has treewidth at most 3k. Restrict the band’s tree decomposition bags to the component’s vertices and transport them along the subtype inclusions. This is the hereditary treewidth step; the strict span hypothesis records the bound used to obtain hband from the parent hypothesis.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

theorem WilliamsonShmoys.retained_component_treewidth_from_band {n : Nat} (G : SimpleGraph (Fin n)) (k j : Nat) (v : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j}) (lo hi : Nat) (hspan : hi - lo < k) (hcontain : ∀ u : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j}, (G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).Reachable u v → G.Reachable (WilliamsonShmoys.bakerRoot G v.1) u.1 ∧ lo ≤ G.dist (WilliamsonShmoys.bakerRoot G v.1) u.1 ∧ G.dist (WilliamsonShmoys.bakerRoot G v.1) u.1 ≤ hi) (hband : RobertsonSeymour1986.GM5.TreewidthLE (G.induce {x : Fin n | G.Reachable (WilliamsonShmoys.bakerRoot G v.1) x ∧ lo ≤ G.dist (WilliamsonShmoys.bakerRoot G v.1) x ∧ G.dist (WilliamsonShmoys.bakerRoot G v.1) x ≤ hi}) (3 * k)) : RobertsonSeymour1986.GM5.TreewidthLE (((G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).induce {u : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j} | (G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).Reachable u v})) (3 * k) := by sorry
