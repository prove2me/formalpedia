-- Prove2me | Theorems.Thm_HypercubeNoStretch_HammingDist_flip
-- name    : HypercubeNoStretch.HammingDist_flip
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:52:37.775389+00:00
-- url     : https://prove2.me/theorems/2e0a0e05-df7e-4808-8ace-767824eb4dd7
-- title:
--   HammingDist flip
-- statement:
--   Formal statement of `HypercubeNoStretch.HammingDist_flip` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem HypercubeNoStretch.HammingDist_flip{k : ℕ} (x y : Cube k) (i : Fin k) (hi : x i ≠ y i) :
--       HammingDist (flipCoord x i) y + 1 = HammingDist x y := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/Combinatorics/HypercubeNoStretch.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/Combinatorics/HypercubeNoStretch.lean#L100

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

theorem HypercubeNoStretch.HammingDist_flip{k : ℕ} (x y : Cube k) (i : Fin k) (hi : x i ≠ y i) :
    HammingDist (flipCoord x i) y + 1 = HammingDist x y := by sorry
