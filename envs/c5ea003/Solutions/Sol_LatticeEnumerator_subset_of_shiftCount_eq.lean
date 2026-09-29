-- Prove2me | solution 1 for LatticeEnumerator.subset_of_shiftCount_eq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:08:42.032056+00:00
-- url     : https://prove2.me/submissions/4690655b-bffd-44d8-a8bb-a26161def75a

-- Sol generated from Cryptography/LatticePointEnumerator.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Theorems.Thm_LatticeEnumerator_mem_shiftLattice
import Theorems.Thm_LatticeEnumerator_shiftLattice_finite

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
theorem solution{P Q : Set (Fin d → ℝ)} (hbP : Bornology.IsBounded P)
    (hbQ : Bornology.IsBounded Q)
    (h : ∀ t : ℝ, 0 < t → ∀ y : Fin d → ℝ, shiftCount P t y = shiftCount Q t y) : P ⊆ Q := by
  obtain ⟨R₁, hR₁⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hbP
  obtain ⟨R₂, hR₂⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hbQ
  set R : ℝ := max (max R₁ R₂) 0 with hRdef
  have hR0 : 0 ≤ R := le_max_right _ _
  have hPR : P ⊆ closedBall 0 R := hR₁.trans (closedBall_subset_closedBall
    (le_trans (le_max_left R₁ R₂) (le_max_left _ _)))
  have hQR : Q ⊆ closedBall 0 R := hR₂.trans (closedBall_subset_closedBall
    (le_trans (le_max_right R₁ R₂) (le_max_left _ _)))
  intro x hx
  set t : ℝ := 1 / (2 * R + 1) with htdef
  have hden : (0 : ℝ) < 2 * R + 1 := by linarith
  have ht : 0 < t := by rw [htdef]; positivity
  have hinv : (1 : ℝ) / t = 2 * R + 1 := by rw [htdef]; field_simp
  -- the origin is counted for `P` at the translate `y = -x`
  have h0 : (0 : Fin d → ℤ) ∈ shiftLattice P t (-x) := by
    have : (fun i => ((0 : Fin d → ℤ) i : ℝ) / t - (-x) i) = x := by
      funext i; simp
    rw [mem_shiftLattice, this]; exact hx
  have hfinQ := shiftLattice_finite hbQ ht (-x)
  have hposP : 0 < shiftCount P t (-x) := by
    rw [shiftCount, Set.ncard_pos (shiftLattice_finite hbP ht (-x))]
    exact ⟨0, h0⟩
  have hposQ : 0 < shiftCount Q t (-x) := by rw [← h t ht (-x)]; exact hposP
  obtain ⟨k, hk⟩ : (shiftLattice Q t (-x)).Nonempty := by
    rw [← Set.ncard_pos hfinQ]; exact hposQ
  -- the counted lattice point must be the origin, because `1/t > 2R`
  have hk0 : k = 0 := by
    funext i
    have hmem : (fun i => (k i : ℝ) / t + x i) ∈ Q := by
      have : (fun i => (k i : ℝ) / t - (-x) i) = fun i => (k i : ℝ) / t + x i := by
        funext j; simp [sub_neg_eq_add]
      rw [mem_shiftLattice] at hk
      rwa [this] at hk
    have hQb : |(k i : ℝ) / t + x i| ≤ R := abs_coord_le_of_mem_closedBall (hQR hmem) i
    have hxb : |x i| ≤ R := abs_coord_le_of_mem_closedBall (hPR hx) i
    have hkb : |(k i : ℝ) / t| ≤ 2 * R := by
      obtain ⟨hQ1, hQ2⟩ := abs_le.1 hQb
      obtain ⟨hx1, hx2⟩ := abs_le.1 hxb
      rw [abs_le]
      constructor <;> linarith
    have hexp : |(k i : ℝ)| * (2 * R + 1) ≤ 2 * R := by
      have : |(k i : ℝ) / t| = |(k i : ℝ)| * (2 * R + 1) := by
        rw [abs_div, abs_of_pos ht, ← hinv]
        field_simp
      linarith [this ▸ hkb]
    have hlt : |(k i : ℝ)| < 1 := by nlinarith [abs_nonneg ((k i : ℝ))]
    have : |k i| < 1 := by exact_mod_cast hlt
    simpa using Int.abs_lt_one_iff.1 this
  rw [hk0] at hk
  simpa using hk
