-- Prove2me | solution 1 for LatticeEnumerator.mem_iff_mem_of_gridRepresentation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:56:01.742368+00:00
-- url     : https://prove2.me/submissions/8def3d74-7562-4f55-a747-635ecb1efc2b

-- Sol generated from Cryptography/LatticePointUniqueness.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointUniqueness
import Theorems.Thm_LatticeEnumerator_eq_of_mem_shiftLattice_of_sparse

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


/-- On a sparse grid the enumerator equals `1` exactly when the distinguished probe point
belongs to `P`. -/
lemma shiftCount_eq_one {P : Set (Fin d → ℝ)} {R t : ℝ} (hP : P ⊆ closedBall 0 R)
    (ht : 0 < t) (h2R : 2 * R < 1 / t) {y : Fin d → ℝ} {k₀ : Fin d → ℤ}
    (hxR : (fun i => (k₀ i : ℝ) / t - y i) ∈ closedBall (0 : Fin d → ℝ) R)
    (hxP : (fun i => (k₀ i : ℝ) / t - y i) ∈ P) : shiftCount P t y = 1 := by
  have hsingle : shiftLattice P t y = {k₀} :=
    Set.eq_singleton_iff_unique_mem.2 ⟨hxP, eq_of_mem_shiftLattice_of_sparse hP ht h2R hxR⟩
  rw [shiftCount, hsingle, Set.ncard_singleton]

/-- On a sparse grid the enumerator vanishes exactly when the distinguished probe point does
not belong to `P`. -/
lemma shiftCount_eq_zero {P : Set (Fin d → ℝ)} {R t : ℝ} (hP : P ⊆ closedBall 0 R)
    (ht : 0 < t) (h2R : 2 * R < 1 / t) {y : Fin d → ℝ} {k₀ : Fin d → ℤ}
    (hxR : (fun i => (k₀ i : ℝ) / t - y i) ∈ closedBall (0 : Fin d → ℝ) R)
    (hxP : (fun i => (k₀ i : ℝ) / t - y i) ∉ P) : shiftCount P t y = 0 := by
  have hempty : shiftLattice P t y = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro k hk
    have hk0 := eq_of_mem_shiftLattice_of_sparse hP ht h2R hxR k hk
    subst hk0
    exact hxP hk
  rw [shiftCount, hempty, Set.ncard_empty]

/-! ## The data determines the indicator at every rational point -/





/-! ## The main uniqueness theorem -/







open LatticeEnumerator in
theorem solution{P Q : Set (Fin d → ℝ)} {R : ℝ} (hR0 : 0 ≤ R)
    (hPR : P ⊆ closedBall 0 R) (hQR : Q ⊆ closedBall 0 R) (h : IntegerTranslateData P Q)
    {x : Fin d → ℝ} {k v : Fin d → ℤ} {s : ℝ} (hs : 2 * R < s)
    (hx : ∀ i, x i = s * (k i : ℝ) - (v i : ℝ)) : x ∈ P ↔ x ∈ Q := by
  have hs0 : 0 < s := lt_of_le_of_lt (by linarith) hs
  set t : ℝ := 1 / s with htdef
  have ht : 0 < t := by rw [htdef]; positivity
  have hinv : 1 / t = s := by rw [htdef, one_div_one_div]
  have h2R : 2 * R < 1 / t := by rw [hinv]; exact hs
  have hprobe : (fun i => (k i : ℝ) / t - ((v i : ℤ) : ℝ)) = x := by
    funext i
    rw [hx i, div_eq_mul_one_div, hinv]
    ring
  by_cases hxR : x ∈ closedBall (0 : Fin d → ℝ) R
  · have hprobeR : (fun i => (k i : ℝ) / t - ((v i : ℤ) : ℝ)) ∈
        closedBall (0 : Fin d → ℝ) R := by rw [hprobe]; exact hxR
    have hdata := h t ht v
    by_cases hxP : x ∈ P
    · by_cases hxQ : x ∈ Q
      · exact iff_of_true hxP hxQ
      · rw [shiftCount_eq_one hPR ht h2R hprobeR (by rw [hprobe]; exact hxP),
          shiftCount_eq_zero hQR ht h2R hprobeR (by rw [hprobe]; exact hxQ)] at hdata
        exact absurd hdata one_ne_zero
    · by_cases hxQ : x ∈ Q
      · rw [shiftCount_eq_zero hPR ht h2R hprobeR (by rw [hprobe]; exact hxP),
          shiftCount_eq_one hQR ht h2R hprobeR (by rw [hprobe]; exact hxQ)] at hdata
        exact absurd hdata.symm one_ne_zero
      · exact iff_of_false hxP hxQ
  · -- outside the bounding ball neither set contains `x`
    exact iff_of_false (fun hmem => hxR (hPR hmem)) (fun hmem => hxR (hQR hmem))
