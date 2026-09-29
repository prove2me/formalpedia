-- Prove2me | Theorems.Thm_TropicalKernelDynamics_tropicalValue_sub_of_sameCell
-- name    : TropicalKernelDynamics.tropicalValue_sub_of_sameCell
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T19:54:13.97907+00:00
-- url     : https://prove2.me/theorems/400e5fed-c499-4eb8-a775-9969117fabce
-- title:
--   The max-plus function is affine on a cell.
-- statement:
--   **The max-plus function is affine on a cell.**  Two points of the same cell differ by the
--   linear form of the cell's piece.
--
--   ```lean
--   theorem TropicalKernelDynamics.tropicalValue_sub_of_sameCell{a : Fin (M + 1) → (Fin P → ℝ)} {b : Fin (M + 1) → ℝ}
--       {x y : Fin P → ℝ} (h : SameTropicalCell (activeSet a b) x y) :
--       tropicalValue a b x - tropicalValue a b y
--         = ∑ j, a (activePiece a b x) j * (x j - y j) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `MachineLearning/TropicalNTKDynamics.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TropicalNTKDynamics.lean#L105

-- Thm stub generated from MachineLearning/TropicalNTKDynamics.lean
import Mathlib
import Definitions.Def_MachineLearning_TropicalNTKDynamics

/-!
# Tropical cells and the freezing of a neural tangent kernel

`MachineLearning/NTKConvergence/Convergence.lean` uses a *tropical cell criterion* as its
geometric source of frozen kernels, but the module it imported for that criterion was
missing from this repository, so the whole `NTKConvergence` chapter failed to build.  This
file supplies it.

The idea is the one behind lazy training of piecewise-linear networks.  A max-plus
("tropical") function

  `T(x) = maxᵢ (⟨aᵢ, x⟩ + bᵢ)`

is affine on each *cell*, the region on which the set of maximizing indices is constant.
Its gradient — and hence any kernel built from the gradient — is therefore literally
constant along a trajectory that stays inside one cell.  `IsCellwiseConstant` abstracts
"constant on cells", `SameTropicalCell` abstracts "in the same cell", and
`tropical_lazy_training_of_cell_invariance` is the resulting freezing statement used
downstream.

## Main results

* `tropical_lazy_training_of_cell_invariance` — a cellwise-constant kernel is constant
  along a cell-confined trajectory.
* `tropicalValue_eq_of_mem_activeSet` — inside a cell the max-plus function *is* one of its
  affine pieces.
* `tropicalValue_sub_of_sameCell` — two points of the same cell differ by the linear form of
  that piece: the function is affine on the cell.
* `activeSetGrad_cellwiseConstant` — consequently the gradient, and any kernel assembled
  from it, is cellwise constant, which is exactly the hypothesis the NTK chapter needs.
-/

open TropicalKernelDynamics

/-! ### The abstract cell framework -/







/-! ### The tropical (max-plus) model that produces such cells -/

variable {M P : ℕ}

theorem TropicalKernelDynamics.tropicalValue_sub_of_sameCell{a : Fin (M + 1) → (Fin P → ℝ)} {b : Fin (M + 1) → ℝ}
    {x y : Fin P → ℝ} (h : SameTropicalCell (activeSet a b) x y) :
    tropicalValue a b x - tropicalValue a b y
      = ∑ j, a (activePiece a b x) j * (x j - y j) := by sorry
