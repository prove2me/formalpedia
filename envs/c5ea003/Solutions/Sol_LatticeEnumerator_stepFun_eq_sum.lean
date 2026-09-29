-- Prove2me | solution 1 for LatticeEnumerator.stepFun_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:05:48.31922+00:00
-- url     : https://prove2.me/submissions/3c772106-9987-4840-b8aa-9c6df23ea8f2

-- Sol generated from Cryptography/LatticePointFourier.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointFourier
import Theorems.Thm_LatticeEnumerator_mem_cube
import Theorems.Thm_LatticeEnumerator_mem_dilLattice

/-!
# Recovering the Fourier transform of an indicator from lattice sums

This file develops the *weighted* form of the Gauss–Weyl counting theorem of
`Cryptography.LatticePointEnumerator`: for a bounded Jordan measurable set `P ⊆ ℝ^d` and a
bounded continuous weight `g`,

`t^{-d} · Σ_{k ∈ tP ∩ ℤ^d} g(k/t) → ∫ 1_P · g`  as `t → ∞`.

Specialising `g` to a character `x ↦ exp(-2πi⟨ξ, x⟩)` shows that the *Fourier transform of the
indicator function* of `P` is recovered, at every frequency `ξ`, as a limit of exponential sums
over the counted lattice points.  This is the analytic content of the "periodic point-counting
function whose Fourier coefficients recover the Fourier transform of the indicator function"
used in the paper.

## Main results

* `LatticeEnumerator.integral_stepFun` : the exact identity
  `∫ 1_{A_t}(x) g(⌊tx⌋/t) dx = t^{-d} Σ_{k ∈ tP ∩ ℤ^d} g(k/t)`.
* `LatticeEnumerator.tendsto_weightedSum` : the weighted counting theorem.
* `LatticeEnumerator.tendsto_fourierSum` : recovery of `∫ 1_P(x) e^{-2πi⟨ξ,x⟩} dx` from the
  lattice exponential sums.
* `LatticeEnumerator.weightedSum_one_eq_dilCount` : consistency check — for `g = 1` the weighted
  theorem specialises to `L_P(t)/t^d → vol P`.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology Complex

open LatticeEnumerator

variable {d : ℕ}













open LatticeEnumerator in
theorem solution{P : Set (Fin d → ℝ)} {t : ℝ} (ht : 0 < t)
    (hfin : (dilLattice P t).Finite) (g : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    (approxSet P t).indicator (fun x => g (floorMap t x)) x
      = ∑ k ∈ hfin.toFinset, (cube t k).indicator (fun _ => g (fun i => (k i : ℝ) / t)) x := by
  by_cases hx : x ∈ approxSet P t
  · set k₀ : Fin d → ℤ := fun i => ⌊t * x i⌋ with hk₀
    have hxk₀ : x ∈ cube t k₀ := (mem_cube ht).2 fun i => rfl
    have hk₀mem : k₀ ∈ hfin.toFinset := by
      rw [hfin.mem_toFinset, mem_dilLattice]
      exact hx
    have hfl : floorMap t x = fun i => (k₀ i : ℝ) / t := rfl
    rw [Set.indicator_of_mem hx, hfl]
    rw [Finset.sum_eq_single k₀]
    · rw [Set.indicator_of_mem hxk₀]
    · intro k _ hne
      refine Set.indicator_of_notMem (fun hmem => hne ?_) _
      exact funext fun i => ((mem_cube ht).1 hmem i).symm
    · intro hnot
      exact absurd hk₀mem hnot
  · rw [Set.indicator_of_notMem hx, Finset.sum_eq_zero]
    intro k hk
    refine Set.indicator_of_notMem (fun hmem => hx ?_) _
    have hfl : floorMap t x = fun i => (k i : ℝ) / t := by
      funext i; simp [floorMap, (mem_cube ht).1 hmem i]
    rw [approxSet, Set.mem_setOf_eq, hfl]
    rw [hfin.mem_toFinset, mem_dilLattice] at hk
    exact hk
