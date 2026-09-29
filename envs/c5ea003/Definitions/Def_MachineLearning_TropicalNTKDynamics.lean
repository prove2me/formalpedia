-- Prove2me | Definitions.Def_MachineLearning_TropicalNTKDynamics
-- name    : MachineLearning_TropicalNTKDynamics
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:24.286539+00:00
-- url     : https://prove2.me/theorems/a379159e-a73c-47e9-87ff-58607a34e18e
-- title:
--   Aether Catalog definitions — MachineLearning_TropicalNTKDynamics
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TropicalNTKDynamics`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TropicalNTKDynamics.lean by skeleton subtraction
import Mathlib

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

namespace TropicalKernelDynamics

/-! ### The abstract cell framework -/

/-- Two points lie in the same cell of the labelling `cellOf`. -/
def SameTropicalCell {α C : Type*} (cellOf : α → C) (x y : α) : Prop := cellOf x = cellOf y




/-- A quantity that depends only on the cell a point lies in. -/
def IsCellwiseConstant {α C β : Type*} (cellOf : α → C) (K : α → β) : Prop :=
  ∀ x y, SameTropicalCell cellOf x y → K x = K y


/-! ### The tropical (max-plus) model that produces such cells -/

variable {M P : ℕ}

/-- A max-plus function `T(x) = maxᵢ (⟨aᵢ, x⟩ + bᵢ)` with `M + 1` affine pieces. -/
noncomputable def tropicalValue (a : Fin (M + 1) → (Fin P → ℝ)) (b : Fin (M + 1) → ℝ)
    (x : Fin P → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i => (∑ j, a i j * x j) + b i

open Classical in
/-- The cell label of `x`: the set of pieces attaining the maximum. -/
noncomputable def activeSet (a : Fin (M + 1) → (Fin P → ℝ)) (b : Fin (M + 1) → ℝ)
    (x : Fin P → ℝ) : Finset (Fin (M + 1)) :=
  Finset.univ.filter fun i => (∑ j, a i j * x j) + b i = tropicalValue a b x

theorem activeSet_nonempty (a : Fin (M + 1) → (Fin P → ℝ)) (b : Fin (M + 1) → ℝ)
    (x : Fin P → ℝ) : (activeSet a b x).Nonempty := by
  classical
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Fin (M + 1)))
      fun i => (∑ j, a i j * x j) + b i
  exact ⟨i, by simp [activeSet, tropicalValue, hi]⟩


/-- The distinguished piece of a cell (the least active index). -/
noncomputable def activePiece (a : Fin (M + 1) → (Fin P → ℝ)) (b : Fin (M + 1) → ℝ)
    (x : Fin P → ℝ) : Fin (M + 1) :=
  (activeSet a b x).min' (activeSet_nonempty a b x)



/-- The gradient of the max-plus function on a cell, i.e. the coefficient vector of the
cell's affine piece. -/
noncomputable def activeSetGrad (a : Fin (M + 1) → (Fin P → ℝ)) (b : Fin (M + 1) → ℝ)
    (x : Fin P → ℝ) : Fin P → ℝ := a (activePiece a b x)




end TropicalKernelDynamics


