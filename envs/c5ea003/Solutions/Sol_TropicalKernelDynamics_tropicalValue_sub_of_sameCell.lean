-- Prove2me | solution 1 for TropicalKernelDynamics.tropicalValue_sub_of_sameCell
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T01:23:22.476499+00:00
-- url     : https://prove2.me/submissions/d6f59691-c2c9-478d-94ed-c43e933a51c0

-- Sol generated from MachineLearning/TropicalNTKDynamics.lean
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




/-- Inside its cell the max-plus function *is* one of its affine pieces. -/
theorem tropicalValue_eq_of_mem_activeSet {a : Fin (M + 1) → (Fin P → ℝ)}
    {b : Fin (M + 1) → ℝ} {x : Fin P → ℝ} {i : Fin (M + 1)} (hi : i ∈ activeSet a b x) :
    tropicalValue a b x = (∑ j, a i j * x j) + b i := by
  classical
  simpa [activeSet, eq_comm] using (Finset.mem_filter.mp hi).2


theorem activePiece_mem (a : Fin (M + 1) → (Fin P → ℝ)) (b : Fin (M + 1) → ℝ)
    (x : Fin P → ℝ) : activePiece a b x ∈ activeSet a b x :=
  Finset.min'_mem _ _







open TropicalKernelDynamics in
theorem solution{a : Fin (M + 1) → (Fin P → ℝ)} {b : Fin (M + 1) → ℝ}
    {x y : Fin P → ℝ} (h : SameTropicalCell (activeSet a b) x y) :
    tropicalValue a b x - tropicalValue a b y
      = ∑ j, a (activePiece a b x) j * (x j - y j) := by
  have hx : tropicalValue a b x = (∑ j, a (activePiece a b x) j * x j) + b (activePiece a b x) :=
    tropicalValue_eq_of_mem_activeSet (activePiece_mem a b x)
  have hmem : activePiece a b x ∈ activeSet a b y := by
    have := activePiece_mem a b x
    rwa [show activeSet a b x = activeSet a b y from h] at this
  have hy : tropicalValue a b y = (∑ j, a (activePiece a b x) j * y j) + b (activePiece a b x) :=
    tropicalValue_eq_of_mem_activeSet hmem
  have hsum : ∑ j, a (activePiece a b x) j * (x j - y j)
      = (∑ j, a (activePiece a b x) j * x j) - ∑ j, a (activePiece a b x) j * y j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hx, hy, hsum]
  ring
