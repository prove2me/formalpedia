-- Prove2me | solution 1 for LatticeEnumerator.ae_eq_of_integerTranslateData
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:00:59.384456+00:00
-- url     : https://prove2.me/submissions/59ebac29-5579-406e-8507-f2221d8df877

-- Sol generated from Cryptography/LatticePointUniqueness.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointUniqueness
import Theorems.Thm_LatticeEnumerator_mem_closure_of_mem_interior_of_data

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
theorem solution{P Q : Set (Fin d → ℝ)}
    (hbP : Bornology.IsBounded P) (hbQ : Bornology.IsBounded Q)
    (hfrP : volume (frontier P) = 0) (hfrQ : volume (frontier Q) = 0)
    (h : IntegerTranslateData P Q) : P =ᵐ[volume] Q := by
  have haeP : ∀ᵐ x : (Fin d → ℝ), x ∉ frontier P := measure_eq_zero_iff_ae_notMem.1 hfrP
  have haeQ : ∀ᵐ x : (Fin d → ℝ), x ∉ frontier Q := measure_eq_zero_iff_ae_notMem.1 hfrQ
  filter_upwards [haeP, haeQ] with x hxP hxQ
  have key : ∀ (A B : Set (Fin d → ℝ)), Bornology.IsBounded A → Bornology.IsBounded B →
      IntegerTranslateData A B → x ∉ frontier A → x ∉ frontier B → x ∈ A → x ∈ B := by
    intro A B hbA hbB hAB hfA hfB hmem
    have hint : x ∈ interior A := by
      by_contra hni
      exact hfA ⟨subset_closure hmem, hni⟩
    have hcl : x ∈ closure B := mem_closure_of_mem_interior_of_data hbA hbB hAB hint
    have : x ∈ interior B := by
      by_contra hni
      exact hfB ⟨hcl, hni⟩
    exact interior_subset this
  have hsymm : IntegerTranslateData Q P := fun t ht v => (h t ht v).symm
  exact eq_iff_iff.2 ⟨fun hm => key P Q hbP hbQ h hxP hxQ hm,
    fun hm => key Q P hbQ hbP hsymm hxQ hxP hm⟩
