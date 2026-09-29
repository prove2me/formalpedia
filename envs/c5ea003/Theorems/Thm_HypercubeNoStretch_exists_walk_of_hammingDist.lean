-- Prove2me | Theorems.Thm_HypercubeNoStretch_exists_walk_of_hammingDist
-- name    : HypercubeNoStretch.exists_walk_of_hammingDist
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:52:48.70616+00:00
-- url     : https://prove2.me/theorems/842710f4-28e6-4a9a-9d32-da56412a7093
-- title:
--   For any two cube vertices there is a hypercube walk between them whose length is exactly the
-- statement:
--   For any two cube vertices there is a hypercube walk between them whose length is exactly the
--   Hamming distance.
--
--   ```lean
--   theorem HypercubeNoStretch.exists_walk_of_hammingDist{k : ℕ} :
--       ∀ (n : ℕ) (x y : Cube k), HammingDist x y = n →
--         ∃ w : (hypercube k).Walk x y, w.length = n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/Combinatorics/HypercubeNoStretch.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/Combinatorics/HypercubeNoStretch.lean#L119

-- Thm stub generated from Applications/Combinatorics/HypercubeNoStretch.lean
import Mathlib
import Definitions.Def_Applications_Combinatorics_HypercubeNoStretch

/-! # No-stretching for labelings into the hypercube over GF(2)

Let `G` be a connected simple graph on `V`, and `ℓ : V → (Fin k → ZMod 2)` a labeling such that
every `G`-edge `{u,v}` satisfies either `ℓ u = ℓ v` or `HammingDist (ℓ u) (ℓ v) = 1`.

We prove that such a labeling does not stretch distances: the hypercube distance between labels is
bounded by the graph distance.

The hypercube `Q_k` has vertex set `Fin k → ZMod 2` and an edge between two vertices at Hamming
distance `1`.

* `hypercube_dist_eq_hammingDist`: the graph distance in `Q_k` equals the Hamming distance.
* `exists_image_walk`: a `G`-walk maps to a hypercube walk of no greater length.
* `no_stretching`: `(hypercube k).dist (ℓ u) (ℓ v) ≤ G.dist u v`.
-/

open SimpleGraph

open HypercubeNoStretch

theorem HypercubeNoStretch.exists_walk_of_hammingDist{k : ℕ} :
    ∀ (n : ℕ) (x y : Cube k), HammingDist x y = n →
      ∃ w : (hypercube k).Walk x y, w.length = n := by sorry
