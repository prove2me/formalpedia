-- Prove2me | solution 1 for GradedTransitivity.eval_one_numerator_of_eventually_const
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:42:14.056402+00:00
-- url     : https://prove2.me/submissions/8dd02128-d1dc-47a6-a6cc-409f82984bf7

-- Sol generated from Shared/GradedTransitivity/Structure.lean
import Mathlib
import Definitions.Def_Shared_GradedTransitivity_FiniteDifference
import Definitions.Def_Shared_GradedTransitivity_GSet
import Definitions.Def_Shared_GradedTransitivity_Structure
import Theorems.Thm_GradedTransitivity_coeff_gen
import Theorems.Thm_GradedTransitivity_constantCoeff_gen

/-!
# The ring of series with poles only at `q = 1`, and the residue at `q = 1`

Two structural refinements of the main theorem.

1. **Algebra.** The power series admitting a denominator `(1-q)^k` form a
   subring `ratOneSubring` of `ℚ[[q]]` (it is the image of the localisation
   `ℚ[X]_{(1-X)}`).  Hilbert series of eventually `r`-transitive graded
   `G`-sets live in it, hence sums and Cauchy products of such Hilbert series
   are again rational with a pole only at `q = 1`.

2. **Residue.** For an eventually `r`-transitive graded `G`-set the pole at
   `q = 1` is *simple with residue `-1`*: if `(1-q)·H(q) = P(q)` then
   `P(1) = 1`.  This is a genuinely quantitative statement — it says the
   numerator of the Hilbert series always evaluates to the eventual number of
   orbits, which is `1` exactly because of transitivity.

## Main results

* `ratOneSubring` and `gen_hilbertSeq_mem_ratOneSubring`.
* `eval_one_numerator_of_eventually_const`, `hilbertSeq_residue_one`.
-/

open GradedTransitivity

open Polynomial

/-! ### The subring of series with denominator a power of `1-q` -/






variable {G : ℕ → Type*} [∀ n, Group (G n)] {Y : ℕ → Type*} [∀ n, MulAction (G n) (Y n)]




/-! ### The residue at `q = 1` -/

/-- Coefficients of the numerator produced by multiplying by `1 - X`. -/
lemma coeff_numerator_zero {a : ℕ → ℚ} {P : ℚ[X]}
    (h : (1 - PowerSeries.X) * gen a = (P : PowerSeries ℚ)) : P.coeff 0 = a 0 := by
  have := congrArg (fun φ => (PowerSeries.coeff 0) φ) h
  simpa using this.symm

lemma coeff_numerator_succ {a : ℕ → ℚ} {P : ℚ[X]} (n : ℕ)
    (h : (1 - PowerSeries.X) * gen a = (P : PowerSeries ℚ)) :
    P.coeff (n + 1) = a (n + 1) - a n := by
  have := congrArg (fun φ => (PowerSeries.coeff (n + 1)) φ) h
  simp only [map_sub, PowerSeries.coeff_succ_X_mul, coeff_gen, Polynomial.coeff_coe,
    sub_mul, one_mul] at this
  simpa using this.symm



variable {G : ℕ → Type*} [∀ n, Group (G n)] {Y : ℕ → Type*} [∀ n, MulAction (G n) (Y n)]




open GradedTransitivity in
theorem solution{a : ℕ → ℚ} {c : ℚ} {N : ℕ} {P : ℚ[X]}
    (hev : ∀ n ≥ N, a n = c) (h : (1 - PowerSeries.X) * gen a = (P : PowerSeries ℚ)) :
    P.eval 1 = c := by
  set m := max N (P.natDegree + 1) with hm
  have hdeg : P.natDegree < m + 1 := by
    have : P.natDegree + 1 ≤ m := le_max_right _ _
    omega
  have hN : N ≤ m := le_max_left _ _
  rw [Polynomial.eval_eq_sum_range' hdeg]
  have hsimp : ∀ i, P.coeff i * (1 : ℚ) ^ i = P.coeff i := by intro i; ring
  simp only [hsimp]
  rw [Finset.sum_range_succ']
  have hterms : ∀ i ∈ Finset.range m, P.coeff (i + 1) = a (i + 1) - a i := by
    intro i _
    exact coeff_numerator_succ i h
  rw [Finset.sum_congr rfl hterms, Finset.sum_range_sub (fun i => a i) m,
    coeff_numerator_zero h]
  have : a m = c := hev m hN
  rw [this]
  ring
