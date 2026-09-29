-- Prove2me | Definitions.Def_Geometry_SublevelDuality_Examples
-- name    : Geometry_SublevelDuality_Examples
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:58:37.144277+00:00
-- url     : https://prove2.me/theorems/f1c98115-9903-49bd-ab8f-1ca04d7c56d4
-- title:
--   Aether Catalog definitions — Geometry_SublevelDuality_Examples
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.SublevelDuality.Examples`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/SublevelDuality/Examples.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_SublevelDuality_Duality
import Definitions.Def_Geometry_SublevelDuality_Homogeneous
-- import output-final_aristotle.output-final_aristotle.Incomplete.Pythagorean.Duality  -- (module absent from the catalog; import removed so the file compiles)

/-
# A concrete, non-vacuous instance of the RC sublevel duality

To certify that the abstract duality of `Duality.lean` is *not vacuous*, we work
out an explicit pair of RC functions on the plane `ℝ × ℝ` whose polarity map is the
coordinate swap `L(x, y) = (y, x)` (a genuine, non-identity continuous linear
equivalence, `ContinuousLinearEquiv.prodComm`).

* `p(x,y) = |x|`,  `q(x,y) = |x| + |y|`   so   `f = p/q = |x| / (|x|+|y|)`.
* `p°(x,y) = |y|`, `q°(x,y) = |x| + |y|`  so   `f° = |y| / (|x|+|y|)`.

These are non-negative, positively homogeneous (degree 1) functions, and the swap
`L` intertwines the two RC functions exactly: `f° ∘ L = f`.  Therefore every
sublevel set of `f` is homeomorphic — via the linear map `L` — to the corresponding
sublevel set of `f°`, and their homology groups agree in all degrees.  This is the
duality of `Duality.lean` instantiated on concrete, visibly distinct subsets of the
plane (two "wedges" pointing along different axes).

## Catalog connections
Instantiates `Geometry.SublevelDuality.sublevelHomeo`, `coneSubHomeo`,
`sublevel_homotopyEquiv` (from `Duality.lean`) on `ratio`/`coneSub` and `IsHomog`
(from `Homogeneous.lean`).
-/

namespace Geometry.SublevelDuality.Examples

open Set Geometry.SublevelDuality

/-- The numerator gauge `p(x,y) = |x|`. -/
noncomputable def pEx : ℝ × ℝ → ℝ := fun v => |v.1|
/-- The denominator gauge `q(x,y) = |x| + |y|`. -/
noncomputable def qEx : ℝ × ℝ → ℝ := fun v => |v.1| + |v.2|
/-- The dual numerator gauge `p°(x,y) = |y|`. -/
noncomputable def pEx' : ℝ × ℝ → ℝ := fun v => |v.2|
/-- The dual denominator gauge `q°(x,y) = |x| + |y|`. -/
noncomputable def qEx' : ℝ × ℝ → ℝ := fun v => |v.1| + |v.2|

/-- The polarity map for this example: the coordinate swap, a linear homeomorphism. -/
noncomputable def swap : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) := ContinuousLinearEquiv.prodComm ℝ ℝ ℝ

-- !-- Lab Notes -- !--
-- Hypothesis (Hypothesizer): the abstract polarity duality must be realisable on
--   an honest, computable pair of RC functions with a non-identity linear map.
-- Experiment (Experimenter): take the axis-wedge ratios `|x|/(|x|+|y|)` and
--   `|y|/(|x|+|y|)` and the coordinate swap; verify homogeneity, non-negativity,
--   and the intertwining identity `f° ∘ swap = f` by `abs_mul` + `add_comm`.
-- Analysis (Analyst): the intertwining is a one-line `add_comm` once the gauges
--   are written out — confirming that *all* the topological force lives in the
--   linearity of the polarity map, exactly as the abstract proof predicts.
-- Critique (Critic): the two sublevel sets are genuinely different subsets of the
--   plane (wedges around the x- vs y-axis), so the homeomorphism is non-trivial;
--   the example rules out the "vacuously equal sets" failure mode.











end Geometry.SublevelDuality.Examples


