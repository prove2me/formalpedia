-- Prove2me | Theorems.Thm_TopeMagnitude_sphere_card
-- name    : TopeMagnitude.sphere_card
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:57:48.406773+00:00
-- url     : https://prove2.me/theorems/7594075b-485a-4007-86c6-b9168948e453
-- title:
--   Sphere card
-- statement:
--   Formal statement of `TopeMagnitude.sphere_card` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TopeMagnitude.sphere_card{n k : ℕ} (x : Fin n → Bool) :
--       Fintype.card (sphere x k) = n.choose k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/TopeMagnitude/Hypercube.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/TopeMagnitude/Hypercube.lean#L119

-- Thm stub generated from Geometry/TopeMagnitude/Hypercube.lean
import Mathlib
import Definitions.Def_Geometry_FlagComplex
import Definitions.Def_Geometry_TopeMagnitude_Hypercube
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

open TopeMagnitude





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



/-
The wall-set map reconstructs every chamber from a fixed base chamber.
-/





/-
**Boolean sphere theorem.**  There are `n choose k` chambers separated from a
fixed chamber by exactly `k` coordinate hyperplanes.
-/

theorem TopeMagnitude.sphere_card{n k : ℕ} (x : Fin n → Bool) :
    Fintype.card (sphere x k) = n.choose k := by sorry
