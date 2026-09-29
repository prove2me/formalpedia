-- Prove2me | Definitions.Def_Applications_Combinatorics_HypercubeNoStretch
-- name    : Applications_Combinatorics_HypercubeNoStretch
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:30.125009+00:00
-- url     : https://prove2.me/theorems/1d41e040-de5a-411f-a717-e0f2d5f20927
-- title:
--   Aether Catalog definitions — Applications_Combinatorics_HypercubeNoStretch
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Combinatorics.HypercubeNoStretch`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Combinatorics/HypercubeNoStretch.lean by skeleton subtraction
import Mathlib

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

namespace HypercubeNoStretch

/-- A vertex of the `k`-dimensional hypercube over `GF(2)`. -/
abbrev Cube (k : ℕ) := Fin k → ZMod 2

/-- Hamming distance: the number of coordinates where `x` and `y` differ. -/
def HammingDist {k : ℕ} (x y : Cube k) : ℕ :=
  (Finset.univ.filter (fun i => x i ≠ y i)).card





/-- The `k`-dimensional hypercube graph over `GF(2)`: two vertices are adjacent iff their Hamming
distance is `1`. -/
def hypercube (k : ℕ) : SimpleGraph (Cube k) :=
  SimpleGraph.fromRel (fun x y => HammingDist x y = 1)



/-- Flip coordinate `i` of `x` (add `1` in `GF(2)`). -/
def flipCoord {k : ℕ} (x : Cube k) (i : Fin k) : Cube k := Function.update x i (x i + 1)





variable {V : Type*} {G : SimpleGraph V} {k : ℕ} {ℓ : V → Cube k}



end HypercubeNoStretch


