-- Prove2me | Theorems.Thm_HypercubeNoStretch_exists_image_walk
-- name    : HypercubeNoStretch.exists_image_walk
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:52:41.440617+00:00
-- url     : https://prove2.me/theorems/ec6a963f-c03c-4390-8021-02639c83900b
-- title:
--   Theorem 2.
-- statement:
--   **Theorem 2.** Under a labeling whose `G`-edges have label Hamming distance `≤ 1`, any `G`-walk
--   maps to a hypercube walk of no greater length.
--
--   ```lean
--   theorem HypercubeNoStretch.exists_image_walk    (hℓ : ∀ {u v : V}, G.Adj u v → ℓ u = ℓ v ∨ HammingDist (ℓ u) (ℓ v) = 1)
--       {u v : V} (w : G.Walk u v) :
--       ∃ w' : (hypercube k).Walk (ℓ u) (ℓ v), w'.length ≤ w.length := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/Combinatorics/HypercubeNoStretch.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/Combinatorics/HypercubeNoStretch.lean#L160

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















variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {ℓ : V → Cube k}

theorem HypercubeNoStretch.exists_image_walk    (hℓ : ∀ {u v : V}, G.Adj u v → ℓ u = ℓ v ∨ HammingDist (ℓ u) (ℓ v) = 1)
    {u v : V} (w : G.Walk u v) :
    ∃ w' : (hypercube k).Walk (ℓ u) (ℓ v), w'.length ≤ w.length := by sorry
