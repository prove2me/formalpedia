-- Prove2me | solution 1 for LatticeEnumerator.eq_of_mem_shiftLattice_of_sparse
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:51:57.019578+00:00
-- url     : https://prove2.me/submissions/fc93ab6e-99dd-4b69-8f91-d857998ad86d

-- Sol generated from Cryptography/LatticePointUniqueness.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointUniqueness

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





/-! ## The main uniqueness theorem -/







open LatticeEnumerator in
theorem solution{P : Set (Fin d → ℝ)} {R t : ℝ} (hP : P ⊆ closedBall 0 R)
    (ht : 0 < t) (h2R : 2 * R < 1 / t) {y : Fin d → ℝ} {k₀ : Fin d → ℤ}
    (hxR : (fun i => (k₀ i : ℝ) / t - y i) ∈ closedBall (0 : Fin d → ℝ) R) :
    ∀ k ∈ shiftLattice P t y, k = k₀ := by
  set x : Fin d → ℝ := fun i => (k₀ i : ℝ) / t - y i with hx
  intro k hk
  by_contra hne
  obtain ⟨j, hj⟩ : ∃ j, k j ≠ k₀ j := by
    by_contra hall
    push_neg at hall
    exact hne (funext hall)
  set z : Fin d → ℝ := fun i => (k i : ℝ) / t - y i with hz
  have hzP : z ∈ closedBall (0 : Fin d → ℝ) R := hP hk
  have hd1 : dist z x ≤ 2 * R := by
    have h1 : dist z 0 ≤ R := by simpa using hzP
    have h2 : dist x 0 ≤ R := by simpa using hxR
    have h3 := dist_triangle z 0 x
    rw [dist_comm (0 : Fin d → ℝ) x] at h3
    linarith
  have hd2 : 1 / t ≤ dist z x := by
    have hcoord : |z j - x j| ≤ dist z x := by
      have hle := dist_le_pi_dist z x j
      rwa [Real.dist_eq] at hle
    have hdiff : |z j - x j| = |(k j : ℝ) - (k₀ j : ℝ)| / t := by
      have hzx : z j - x j = ((k j : ℝ) - (k₀ j : ℝ)) / t := by
        rw [hz, hx]; ring
      rw [hzx, abs_div, abs_of_pos ht]
    have hone : (1 : ℝ) ≤ |(k j : ℝ) - (k₀ j : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |k j - k₀ j| := Int.one_le_abs (sub_ne_zero.2 hj)
      have h2 : ((1 : ℤ) : ℝ) ≤ ((|k j - k₀ j| : ℤ) : ℝ) := by exact_mod_cast h1
      rwa [Int.cast_abs, Int.cast_sub, Int.cast_one] at h2
    calc 1 / t ≤ |(k j : ℝ) - (k₀ j : ℝ)| / t := by gcongr
      _ = |z j - x j| := hdiff.symm
      _ ≤ dist z x := hcoord
  linarith
