-- Prove2me | solution 1 for LatticeEnumerator.shiftLattice_finite
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:02:43.205738+00:00
-- url     : https://prove2.me/submissions/bf092720-e223-4513-8290-8e19ae86bb80

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

/-- In the sup-metric on `ℝ^d`, membership in a closed ball bounds every coordinate. -/
lemma abs_coord_le_of_mem_closedBall {R : ℝ} {z : Fin d → ℝ}
    (h : z ∈ closedBall (0 : Fin d → ℝ) R) (i : Fin d) : |z i| ≤ R := by
  simp only [mem_closedBall, dist_zero_right] at h
  have hi : ‖z i‖ ≤ ‖z‖ := norm_le_pi_norm z i
  rw [Real.norm_eq_abs] at hi
  linarith



/-! ## The cube decomposition -/









/-! ## The rounding map and pointwise convergence -/




/-! ## The Gauss–Weyl counting theorem -/




/-! ## Rigidity for real translates -/




open LatticeEnumerator in
theorem solution{P : Set (Fin d → ℝ)} (hP : Bornology.IsBounded P) {t : ℝ} (ht : 0 < t)
    (y : Fin d → ℝ) : (shiftLattice P t y).Finite := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hP
  set B : ℝ := (R + ‖y‖) * t with hB
  have hsub : shiftLattice P t y ⊆
      (Set.univ.pi fun _ : Fin d => Set.Icc (⌈-B⌉) (⌊B⌋) : Set (Fin d → ℤ)) := by
    intro k hk i _
    have h1 : |(k i : ℝ) / t - y i| ≤ R := abs_coord_le_of_mem_closedBall (hR hk) i
    have h2 : |y i| ≤ ‖y‖ := by
      have := norm_le_pi_norm y i
      rwa [Real.norm_eq_abs] at this
    have h3 : |(k i : ℝ) / t| ≤ R + ‖y‖ := by
      calc |(k i : ℝ) / t| = |((k i : ℝ) / t - y i) + y i| := by ring_nf
        _ ≤ |(k i : ℝ) / t - y i| + |y i| := abs_add_le _ _
        _ ≤ R + ‖y‖ := add_le_add h1 h2
    have h4 : |(k i : ℝ)| ≤ B := by
      rw [hB, abs_div, abs_of_pos ht] at *
      calc |(k i : ℝ)| = |(k i : ℝ)| / t * t := by field_simp
        _ ≤ (R + ‖y‖) * t := mul_le_mul_of_nonneg_right h3 ht.le
    refine ⟨?_, ?_⟩
    · exact_mod_cast Int.ceil_le.2 (by exact_mod_cast neg_le_of_abs_le h4)
    · exact Int.le_floor.2 (by exact_mod_cast le_of_abs_le h4)
  exact Set.Finite.subset (Set.Finite.pi fun _ => Set.finite_Icc _ _) hsub
