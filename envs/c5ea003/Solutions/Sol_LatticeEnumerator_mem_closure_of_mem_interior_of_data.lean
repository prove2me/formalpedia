-- Prove2me | solution 1 for LatticeEnumerator.mem_closure_of_mem_interior_of_data
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:59:34.235556+00:00
-- url     : https://prove2.me/submissions/3d72003c-4b54-425a-a3bb-4889a8ffc98d

-- Sol generated from Cryptography/LatticePointUniqueness.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointUniqueness
import Theorems.Thm_LatticeEnumerator_dist_floorMap_le
import Theorems.Thm_LatticeEnumerator_mem_iff_mem_of_integerTranslateData

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




/-- Rational points can be produced by rounding: `floorMap N x` is a rational point at
sup-distance at most `1/N` from `x`. -/
lemma exists_rational_point_close {x : Fin d → ℝ} {ε : ℝ} (hε : 0 < ε) :
    ∃ (N : ℕ) (a : Fin d → ℤ), 0 < N ∧ dist (fun i => (a i : ℝ) / (N : ℝ)) x < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n + 1, fun i => ⌊((n : ℝ) + 1) * x i⌋, Nat.succ_pos n, ?_⟩
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hd : dist (floorMap ((n : ℝ) + 1) x) x ≤ 1 / ((n : ℝ) + 1) := dist_floorMap_le hpos x
  have hfl : (fun i => ((⌊((n : ℝ) + 1) * x i⌋ : ℤ) : ℝ) / ((n + 1 : ℕ) : ℝ))
      = floorMap ((n : ℝ) + 1) x := by
    funext i
    simp [floorMap]
  rw [hfl]
  exact lt_of_le_of_lt hd hn

/-! ## The main uniqueness theorem -/







open LatticeEnumerator in
theorem solution{P Q : Set (Fin d → ℝ)}
    (hbP : Bornology.IsBounded P) (hbQ : Bornology.IsBounded Q) (h : IntegerTranslateData P Q)
    {x : Fin d → ℝ} (hx : x ∈ interior P) : x ∈ closure Q := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior x hx
  rw [Metric.mem_closure_iff]
  intro δ hδ
  obtain ⟨N, a, hN, hdist⟩ := exists_rational_point_close (x := x) (ε := min δ ε)
    (lt_min hδ hε)
  refine ⟨fun i => (a i : ℝ) / (N : ℝ), ?_, ?_⟩
  · refine (mem_iff_mem_of_integerTranslateData hbP hbQ h N hN a).1 ?_
    refine interior_subset (hball ?_)
    rw [mem_ball]
    exact lt_of_lt_of_le hdist (min_le_right _ _)
  · rw [dist_comm]
    exact lt_of_lt_of_le hdist (min_le_left _ _)
