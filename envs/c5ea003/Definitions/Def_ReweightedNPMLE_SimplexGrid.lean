-- Prove2me | Definitions.Def_ReweightedNPMLE_SimplexGrid
-- name    : ReweightedNPMLE_SimplexGrid
-- status  : Definition
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:24:34.320131+00:00
-- url     : https://prove2.me/theorems/8c569796-e6af-4a2f-89be-84838f597861
-- title:
--   Denominator grids and mass-preserving rounding for simplex weights
-- statement:
--   For \(k\ge0\) and denominator \(M>0\), define \(F_M(x)=\lfloor Mx\rfloor_{\mathbb N}/M\), where \(\lfloor t\rfloor_{\mathbb N}=\max\{0,\lfloor t\rfloor\}\). A vector \(w=(w_1,\ldots,w_{k+1})\) is rounded by applying \(F_M\) to its first \(k\) coordinates and assigning the residual \(1-\sum_{j=1}^kF_M(w_j)\) to the last coordinate. The ambient finite grid consists of
--   \[
--   (a_1/M,\ldots,a_k/M,\ 1-\textstyle\sum_{j=1}^k a_j/M),
--   \qquad a_j\in\{0,\ldots,M\}.
--   \]
--   The valid grid retains exactly the nonnegative vectors. Every ambient grid vector has total mass one, while the validity condition enforces membership in the simplex. The same formulas are defined at \(M=0\) using zero for division by zero.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/SimplexGrid.lean#L16-L225

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Tactic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Finite simplex-grid rounding

The deterministic denominator-grid construction used to discretize the
Carathéodory mixture weights in the likelihood net.
-/

open scoped BigOperators

namespace ReweightedNPMLE

/-- Round a nonnegative real down to the nearest multiple of `1 / M`. -/
noncomputable def nonnegativeGridFloor (M : ℕ) (x : ℝ) : ℝ :=
  (⌊(M : ℝ) * x⌋₊ : ℝ) / M







/-- Round every coordinate except the last down to the denominator-`M` grid;
the last coordinate receives the remaining mass. -/
noncomputable def simplexGridRound (k M : ℕ)
    (w : Fin (k + 1) → ℝ) : Fin (k + 1) → ℝ :=
  fun i ↦ if i = Fin.last k then
      1 - ∑ j ∈ (Finset.univ.erase (Fin.last k)), nonnegativeGridFloor M (w j)
    else nonnegativeGridFloor M (w i)

















/-- A point in the denominator-`M` simplex weight grid.  The first `k`
coordinates are grid multiples; the final coordinate receives the residual,
so every grid point has total mass one. -/
noncomputable def simplexGridPoint (k M : ℕ)
    (a : Fin k → Fin (M + 1)) : Fin (k + 1) → ℝ :=
  Fin.snoc (fun i ↦ (a i : ℝ) / M)
    (1 - ∑ i, (a i : ℝ) / M)



/-- The finite denominator-`M` grid of simplex weights with `k+1` slots. -/
noncomputable def simplexWeightGrid (k M : ℕ) :
    Finset (Fin (k + 1) → ℝ) :=
  Finset.univ.image (simplexGridPoint k M)



/-- The valid part of the ambient weight grid, obtained by retaining only
nonnegative vectors.  Every such vector already has total mass one. -/
noncomputable def validSimplexWeightGrid (k M : ℕ) :
    Finset (Fin (k + 1) → ℝ) :=
  (simplexWeightGrid k M).filter fun w ↦ ∀ i, 0 ≤ w i













end ReweightedNPMLE


