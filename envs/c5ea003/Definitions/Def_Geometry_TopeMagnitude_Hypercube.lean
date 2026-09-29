-- Prove2me | Definitions.Def_Geometry_TopeMagnitude_Hypercube
-- name    : Geometry_TopeMagnitude_Hypercube
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T01:00:14.388091+00:00
-- url     : https://prove2.me/theorems/3c8293f1-ba71-4417-9c5c-a48c645b47b1
-- title:
--   Aether Catalog definitions — Geometry_TopeMagnitude_Hypercube
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.TopeMagnitude.Hypercube`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/TopeMagnitude/Hypercube.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_FlagComplex
/-!
# Sign vectors, hyperplane separation, and the coordinate tope graph

A chamber of the coordinate hyperplane arrangement is a sign vector.  Crossing a
wall changes one sign, so its tope graph is the Boolean hypercube.  The results
below isolate two structural ingredients used in magnitude-homological
computations: wall separation gives the graph metric, and metric spheres are
counted by the Boolean face numbers.

-- !-- Lab Notes -- !--
Hypothesis: the distance between two coordinate chambers is exactly the number of
hyperplanes separating them, and the chambers at distance `k` are naturally the
`k`-faces of the Boolean simplex.
Experiment: encode chambers by Boolean sign vectors and wall sets by finite subsets.
The flip operation was tested in dimensions zero through five; sphere rows are
`[1]`, `[1,1]`, `[1,2,1]`, `[1,3,3,1]`, `[1,4,6,4,1]`, and
`[1,5,10,10,5,1]`.
Analysis: every changed coordinate forces a crossing, while flipping precisely the
separating coordinates realizes the lower bound.  Thus geometric distance and
Boolean rank coincide.
Critique: this proves the complete coordinate-arrangement case, not the general
Edelman--Walker or Alexander-duality step.  No realizability assumption is hidden:
all statements concern the explicitly defined coordinate arrangement.
Synthesis: `hamming_triangle`, `flip_hamming`, and `sphere_card` provide a reusable
metric-enumerative bridge.  The imported flag-complex theory identifies the full
simplex as the clique complex of its complete one-skeleton.
-- !-- Lab Notes -- !--
-/

open Finset

namespace TopeMagnitude

/-- The set of coordinate hyperplanes separating two sign vectors. -/
def separatingWalls {n : ℕ} (x y : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun i => x i ≠ y i

/-- Hamming distance, interpreted as the number of separating hyperplanes. -/
def hamming {n : ℕ} (x y : Fin n → Bool) : ℕ := (separatingWalls x y).card



/-
Separation is symmetric in the two chambers.
-/

/-
A wall separating the endpoints separates at least one of the two successive
pairs.  This is the coordinate form of the wall-crossing lower bound.
-/

/-
The number of separating hyperplanes satisfies the triangle inequality.
-/

/-- Flip exactly the signs indexed by `s`. -/
def flip {n : ℕ} (x : Fin n → Bool) (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ s then !x i else x i


/-
The wall-set map reconstructs every chamber from a fixed base chamber.
-/



/-- A metric sphere in the coordinate tope graph. -/
def sphere {n : ℕ} (x : Fin n → Bool) (k : ℕ) :=
  {y : Fin n → Bool // hamming x y = k}

noncomputable instance sphereFintype {n : ℕ} (x : Fin n → Bool) (k : ℕ) :
    Fintype (sphere x k) := by
  classical
  unfold sphere
  infer_instance

/-
**Boolean sphere theorem.**  There are `n choose k` chambers separated from a
fixed chamber by exactly `k` coordinate hyperplanes.
-/


/-
The total number of coordinate chambers is recovered by summing its metric
spheres.
-/

end TopeMagnitude


