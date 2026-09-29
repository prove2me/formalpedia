-- Prove2me | Definitions.Def_Cryptography_LatticePointEnumerator
-- name    : Cryptography_LatticePointEnumerator
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:19:07.630715+00:00
-- url     : https://prove2.me/theorems/c2b11623-0eb3-40d1-b35c-06a8b622ccdb
-- title:
--   Aether Catalog definitions — Cryptography_LatticePointEnumerator
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.LatticePointEnumerator`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/LatticePointEnumerator.lean by skeleton subtraction
import Mathlib

/-!
# Lattice-point enumerators: asymptotics and rigidity

This file formalises the analytic core of the theory of *lattice-point enumerators*
`L_P(t) = |tP ∩ ℤ^d|` (`t > 0` a **real** dilation parameter) for bounded sets
`P ⊆ ℝ^d`, in the setting of the paper *A Fourier-analytic uniqueness theorem for
lattice-point enumerators*.

## Main definitions

* `LatticeEnumerator.shiftLattice P t y` : the set `{k ∈ ℤ^d : k/t - y ∈ P}` of lattice
  points of the dilated translate `t·(P + y)`.
* `LatticeEnumerator.dilLattice P t` : the lattice points `tP ∩ ℤ^d` (the case `y = 0`).
* `LatticeEnumerator.dilCount P t` : the lattice-point enumerator `L_P(t) = |tP ∩ ℤ^d|`.
* `LatticeEnumerator.shiftCount P t y` : the translated enumerator `|t(P + y) ∩ ℤ^d|`.
* `LatticeEnumerator.cube t k`, `LatticeEnumerator.floorMap t`,
  `LatticeEnumerator.approxSet P t` : the half-open `1/t`-cube attached to a lattice point,
  the coordinatewise rounding map `x ↦ ⌊t x⌋ / t`, and the union of the cubes attached to
  the counted lattice points.

## Main results

* `LatticeEnumerator.volume_approxSet` : the *exact* geometric identity
  `vol(A_t) = L_P(t) · t^{-d}`, where `A_t = {x : ⌊tx⌋/t ∈ P}` is a union of `L_P(t)`
  pairwise disjoint cubes of side `1/t`.
* `LatticeEnumerator.tendsto_dilCount_div` : the Gauss–Weyl counting theorem
  `L_P(t)/t^d → vol(P)` as `t → ∞`, for every bounded set with null topological frontier
  (Jordan measurable set).  The proof combines the exact identity above with dominated
  convergence, the domination coming from the fact that all the sets `A_t`, `t ≥ 1`, live
  in one fixed ball.
* `LatticeEnumerator.volume_eq_of_dilCount_eq` : two bounded Jordan measurable sets with
  the same real-parameter enumerator have the same volume.
* `LatticeEnumerator.volume_eq_of_dilCount_eq_convex` : the same statement for convex
  bodies, where Jordan measurability is automatic.
* `LatticeEnumerator.eq_of_shiftCount_eq` : a rigidity theorem.  If the enumerators of
  **all real translates** of two bounded sets agree, the sets are *equal* (not merely equal
  almost everywhere).  This isolates exactly where the difficulty of the integer-translate
  theorem lies: with real translates the periodisation is faithful at small `t`.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology

namespace LatticeEnumerator

variable {d : ℕ}

/-! ## Definitions -/

/-- `shiftLattice P t y = {k ∈ ℤ^d : k/t - y ∈ P}`, i.e. the set of lattice points of the
dilated translate `t · (P + y)`. -/
def shiftLattice (P : Set (Fin d → ℝ)) (t : ℝ) (y : Fin d → ℝ) : Set (Fin d → ℤ) :=
  {k | (fun i => (k i : ℝ) / t - y i) ∈ P}

/-- `dilLattice P t = tP ∩ ℤ^d`, viewed inside `ℤ^d`. -/
def dilLattice (P : Set (Fin d → ℝ)) (t : ℝ) : Set (Fin d → ℤ) := shiftLattice P t 0

/-- The translated lattice-point enumerator `|t(P + y) ∩ ℤ^d|`. -/
def shiftCount (P : Set (Fin d → ℝ)) (t : ℝ) (y : Fin d → ℝ) : ℕ := (shiftLattice P t y).ncard

/-- The lattice-point enumerator `L_P(t) = |tP ∩ ℤ^d|`. -/
def dilCount (P : Set (Fin d → ℝ)) (t : ℝ) : ℕ := (dilLattice P t).ncard

/-- The half-open cube of side `1/t` with lower corner the lattice point `k/t`. -/
def cube (t : ℝ) (k : Fin d → ℤ) : Set (Fin d → ℝ) :=
  Set.univ.pi fun i => Set.Ico ((k i : ℝ) / t) (((k i : ℝ) + 1) / t)

/-- Coordinatewise rounding to the grid `(1/t)ℤ^d`. -/
def floorMap (t : ℝ) (x : Fin d → ℝ) : Fin d → ℝ := fun i => (⌊t * x i⌋ : ℝ) / t

/-- The set `A_t = {x : ⌊tx⌋/t ∈ P}`; it is the union of the `1/t`-cubes attached to the
lattice points counted by `L_P(t)`. -/
def approxSet (P : Set (Fin d → ℝ)) (t : ℝ) : Set (Fin d → ℝ) := {x | floorMap t x ∈ P}



/-! ## Finiteness of the counted lattice sets -/




/-! ## The cube decomposition -/









/-! ## The rounding map and pointwise convergence -/




/-! ## The Gauss–Weyl counting theorem -/




/-! ## Rigidity for real translates -/



end LatticeEnumerator


