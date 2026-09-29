-- Prove2me | solution 1 for RLHF.exp_sample_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:34:41.540667+00:00
-- url     : https://prove2.me/submissions/2e9be956-3420-4b3a-af59-d9e934167fdf

-- Sol generated from NumberTheory/RLHFPronySampling.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFPronySampling
import Definitions.Def_NumberTheory_RLHFSpectralRigidity

/-!
# Finite-sample spectral rigidity: how many temperatures does a reward audit need?

`RLHF.spectral_rigidity` recovers the reward spectrum of an RLHF problem from the value of
the partition function at *every* positive temperature.  This file makes the statement
finite, in both directions, settling the two-atom case of the "Prony count" conjecture
recorded in `FUTURE_DIRECTIONS.md`.

* `RLHF.exp_sample_uniqueness` — **known levels, `n` samples suffice.**  If the candidate
  reward levels `v₀, …, v_{n-1}` are known and distinct, then the masses carried by them are
  determined by the partition function at the `n` arithmetically spaced inverse temperatures
  `t₀, t₀ + τ, …, t₀ + (n−1)τ`.  The engine is a *generalized Vandermonde* determinant: on an
  arithmetic grid of temperatures the exponential-sum system becomes an honest Vandermonde
  system in the variables `e^{v_j τ}`, which are distinct because `exp` is injective.
* `RLHF.spectral_rigidity_sampled` — the RLHF form of the same statement: two RLHF problems
  whose reward values lie in a common known finite list and whose partition functions agree
  at `n` equally spaced inverse temperatures have identical reward spectra.
* `RLHF.prony_three_samples_insufficient` — **unknown levels: three temperatures are not
  enough.**  Two explicit two-atom RLHF problems on `Bool`, with pairwise distinct reward
  levels, whose partition functions agree at the three inverse temperatures `t = 0, 1, 2`,
  and whose reward spectra differ.  The construction is a moment coincidence: the two-point
  distributions `{1, 3}` with masses `(1/2, 1/2)` and `{3/2, 4}` with masses `(4/5, 1/5)`
  have the same mean `2` and the same second moment `5`, and taking logarithms of the
  support turns those two moment equations into agreement of the partition functions at
  `t = 1` and `t = 2` (agreement at `t = 0` being normalization).

Together: the sampling count is governed by whether the reward *levels* are known.  With
known levels `n` measurements are enough; with unknown levels, `2n − 1 = 3` measurements are
provably not enough for `n = 2` atoms.
-/

open RLHF

open Finset

/-! ## 1. Known levels: an arithmetic grid of `n` temperatures suffices -/



/-! ## 2. Unknown levels: three temperatures are not enough -/









open RLHF in
theorem solution{n : ℕ} {v : Fin n → ℝ} (hv : Function.Injective v)
    {t₀ tau : ℝ} (htau : tau ≠ 0) {a b : Fin n → ℝ}
    (h : ∀ i : Fin n, ∑ j, a j * Real.exp (v j * (t₀ + (i : ℕ) * tau))
      = ∑ j, b j * Real.exp (v j * (t₀ + (i : ℕ) * tau))) :
    a = b := by
  classical
  set x : Fin n → ℝ := fun j => Real.exp (v j * tau) with hxdef
  have hxinj : Function.Injective x := by
    intro j k hjk
    have h1 : v j * tau = v k * tau := Real.exp_eq_exp.mp hjk
    exact hv (mul_right_cancel₀ htau h1)
  have hdet : (Matrix.vandermonde x).det ≠ 0 := by
    rw [Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_))
    have hij : i ≠ j := ne_of_lt (Finset.mem_Ioi.mp hj)
    exact sub_ne_zero.mpr (fun hc => hij (hxinj hc).symm)
  set c : Fin n → ℝ := fun j => (a j - b j) * Real.exp (v j * t₀) with hcdef
  have hmul : Matrix.mulVec (Matrix.transpose (Matrix.vandermonde x)) c = 0 := by
    funext i
    have hi := h i
    have hterm : ∀ j : Fin n, x j ^ (i : ℕ) * c j
        = a j * Real.exp (v j * (t₀ + (i : ℕ) * tau))
          - b j * Real.exp (v j * (t₀ + (i : ℕ) * tau)) := by
      intro j
      have hexp : Real.exp (v j * tau) ^ (i : ℕ) * Real.exp (v j * t₀)
          = Real.exp (v j * (t₀ + (i : ℕ) * tau)) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        congr 1
        ring
      simp only [hxdef, hcdef]
      calc Real.exp (v j * tau) ^ (i : ℕ) * ((a j - b j) * Real.exp (v j * t₀))
          = (a j - b j) * (Real.exp (v j * tau) ^ (i : ℕ) * Real.exp (v j * t₀)) := by ring
        _ = (a j - b j) * Real.exp (v j * (t₀ + (i : ℕ) * tau)) := by rw [hexp]
        _ = a j * Real.exp (v j * (t₀ + (i : ℕ) * tau))
              - b j * Real.exp (v j * (t₀ + (i : ℕ) * tau)) := by ring
    simp only [Matrix.mulVec, Matrix.transpose_apply, Matrix.vandermonde_apply, dotProduct,
      Pi.zero_apply]
    rw [Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib, hi, sub_self]
  have hc0 : c = 0 :=
    Matrix.eq_zero_of_mulVec_eq_zero (M := Matrix.transpose (Matrix.vandermonde x))
      (by rwa [Matrix.det_transpose]) hmul
  funext j
  have hj := congrFun hc0 j
  rw [hcdef] at hj
  simp only [Pi.zero_apply] at hj
  have hexp : Real.exp (v j * t₀) ≠ 0 := (Real.exp_pos _).ne'
  have : a j - b j = 0 := by
    rcases mul_eq_zero.mp hj with h1 | h1
    · exact h1
    · exact absurd h1 hexp
  linarith
