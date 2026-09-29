-- Prove2me | solution 1 for LatticeEnumerator.mem_iff_mem_of_integerTranslateData
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:58:13.977784+00:00
-- url     : https://prove2.me/submissions/2d0b6d6f-be5e-4fbb-941f-1b360138efdb

-- Sol generated from Cryptography/LatticePointUniqueness.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointUniqueness
import Theorems.Thm_LatticeEnumerator_mem_iff_mem_of_gridRepresentation

/-!
# A uniqueness theorem for lattice-point enumerators of integer translates

Let `P ⊆ ℝ^d` be bounded and let

`L_{P+v}(t) = |t(P+v) ∩ ℤ^d|`,  `t > 0` real, `v ∈ ℤ^d`,

be the family of real-parameter lattice-point enumerators of all *integer* translates of `P`
(`LatticeEnumerator.shiftCount P t v`).  The main theorem of the paper
*A Fourier-analytic uniqueness theorem for lattice-point enumerators* states that this data
determines the indicator function of `P` almost everywhere, provided `P` is bounded,
measurable and has null topological frontier.

This file gives a complete, **elementary** proof of that statement (and of a strictly stronger
pointwise statement), avoiding Fourier analysis altogether.

## The mechanism

Fix a rational point `x = a/N ∈ ℚ^d` and put

`M = ⌈2R⌉ + 2`,  `q = N·M + 1`,  `t = N/q`,  `v = M·a ∈ ℤ^d`,

where `P ∪ Q ⊆ closedBall 0 R`.  The counted grid `(1/t)ℤ^d - v = (q/N)ℤ^d - M a` has spacing
`q/N = M + 1/N > 2R`, hence **at most one** of its points can lie in the ball of radius `R`;
and the lattice point `k = a` produces exactly the probe point

`a/t - v = a(M + 1/N) - M a = a/N = x`.

Consequently `L_{P+v}(t) = 1` if `x ∈ P` and `= 0` otherwise: the enumerator data *reads off*
the indicator of `P` at every rational point (`mem_iff_mem_of_integerTranslateData`).
Since `ℚ^d` is dense and, off the (null) frontier, membership is a local property, the
indicators agree almost everywhere.

## Main results

* `LatticeEnumerator.shiftCount_eq_one`, `LatticeEnumerator.shiftCount_eq_zero` : the
  sparse-grid evaluation lemmas.
* `LatticeEnumerator.mem_iff_mem_of_gridRepresentation` : the master lemma — membership is
  determined at every point of the form `s·k - v` with `k, v ∈ ℤ^d` and `s` large.
* `LatticeEnumerator.mem_iff_mem_of_integerTranslateData` : the data determines membership at
  every rational point — *exactly*, with no regularity hypothesis whatsoever.
* `LatticeEnumerator.ae_eq_of_integerTranslateData` : the paper's theorem, `P =ᵐ Q`, for
  bounded sets with null frontier.
* `LatticeEnumerator.volume_symmDiff_eq_zero_of_integerTranslateData` : the same, stated as
  `vol(P Δ Q) = 0`.
* `LatticeEnumerator.convexBody_eq_of_integerTranslateData` : the corollary for convex bodies:
  interiors and closures coincide.
* `LatticeEnumerator.eq_of_integerTranslateData_dim_one` : in dimension one the conclusion
  upgrades to exact set equality, with no measurability or frontier hypothesis.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology

open LatticeEnumerator

variable {d : ℕ}



/-! ## Reading off the indicator on a sparse grid -/




/-! ## The data determines the indicator at every rational point -/


/-- A common bounding radius for two bounded sets, chosen nonnegative. -/
lemma exists_common_radius {P Q : Set (Fin d → ℝ)} (hbP : Bornology.IsBounded P)
    (hbQ : Bornology.IsBounded Q) :
    ∃ R : ℝ, 0 ≤ R ∧ P ⊆ closedBall 0 R ∧ Q ⊆ closedBall 0 R := by
  obtain ⟨R₁, hR₁⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hbP
  obtain ⟨R₂, hR₂⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hbQ
  refine ⟨max (max R₁ R₂) 0, le_max_right _ _, ?_, ?_⟩
  · exact hR₁.trans (closedBall_subset_closedBall
      (le_trans (le_max_left R₁ R₂) (le_max_left _ _)))
  · exact hR₂.trans (closedBall_subset_closedBall
      (le_trans (le_max_right R₁ R₂) (le_max_left _ _)))



/-! ## The main uniqueness theorem -/







open LatticeEnumerator in
theorem solution{P Q : Set (Fin d → ℝ)}
    (hbP : Bornology.IsBounded P) (hbQ : Bornology.IsBounded Q) (h : IntegerTranslateData P Q)
    (N : ℕ) (hN : 0 < N) (a : Fin d → ℤ) :
    (fun i => (a i : ℝ) / (N : ℝ)) ∈ P ↔ (fun i => (a i : ℝ) / (N : ℝ)) ∈ Q := by
  obtain ⟨R, hR0, hPR, hQR⟩ := exists_common_radius hbP hbQ
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- the sparse grid: spacing `s = M + 1/N`, lattice point `k = a`, translate `v = M · a`
  set M : ℕ := ⌈2 * R⌉₊ + 2 with hM
  set s : ℝ := (M : ℝ) + 1 / (N : ℝ) with hsdef
  have hs : 2 * R < s := by
    have h1 : 2 * R ≤ (⌈2 * R⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈2 * R⌉₊ : ℝ) + 2 = (M : ℝ) := by rw [hM]; push_cast; ring
    have h3 : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    rw [hsdef]; linarith
  refine mem_iff_mem_of_gridRepresentation hR0 hPR hQR h (k := a) (v := fun i => (M : ℤ) * a i)
    (s := s) hs ?_
  intro i
  rw [hsdef]
  push_cast
  field_simp
  ring
