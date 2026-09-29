-- Prove2me | solution 1 for LatticeEnumerator.dist_floorMap_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:51:56.509952+00:00
-- url     : https://prove2.me/submissions/a928697d-c062-4ed1-b1c6-08d5e2a452a3

-- Sol generated from Cryptography/LatticePointEnumerator.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator

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

open LatticeEnumerator

variable {d : ℕ}

/-! ## Definitions -/










/-! ## Finiteness of the counted lattice sets -/




/-! ## The cube decomposition -/









/-! ## The rounding map and pointwise convergence -/




/-! ## The Gauss–Weyl counting theorem -/




/-! ## Rigidity for real translates -/




open LatticeEnumerator in
theorem solution{t : ℝ} (ht : 0 < t) (x : Fin d → ℝ) : dist (floorMap t x) x ≤ 1 / t := by
  refine (dist_pi_le_iff (by positivity)).2 fun i => ?_
  have h1 : (⌊t * x i⌋ : ℝ) ≤ t * x i := Int.floor_le _
  have h2 : t * x i - 1 < (⌊t * x i⌋ : ℝ) := Int.sub_one_lt_floor _
  have hrw : (⌊t * x i⌋ : ℝ) / t - x i = ((⌊t * x i⌋ : ℝ) - t * x i) / t := by
    field_simp
  rw [Real.dist_eq, floorMap, hrw, abs_div, abs_of_pos ht]
  gcongr
  rw [abs_le]
  constructor <;> linarith
