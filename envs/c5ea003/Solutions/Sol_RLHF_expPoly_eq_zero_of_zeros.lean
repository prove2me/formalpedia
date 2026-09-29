-- Prove2me | solution 1 for RLHF.expPoly_eq_zero_of_zeros
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:34:40.31199+00:00
-- url     : https://prove2.me/submissions/9aa169f0-a0bb-4ad0-b7bc-e457cdcf95e7

-- Sol generated from NumberTheory/RLHFChebyshevSystem.lean
import Mathlib
import Definitions.Def_NumberTheory_RLHFPronySampling
import Theorems.Thm_RLHF_hasDerivAt_expPoly

/-!
# Exponential sums form a Chebyshev system: `n` arbitrary temperatures suffice

`RLHF.exp_sample_uniqueness` recovers the masses on `n` known reward levels from the
partition function at `n` *arithmetically spaced* inverse temperatures, by a Vandermonde
determinant.  This file removes the arithmetic-grid hypothesis: **any** `n` distinct
temperatures do.

The engine is the classical Descartes/Chebyshev fact, proved here by induction on the number
of exponents with Rolle's theorem supplying the inductive step:

* `RLHF.expPoly_eq_zero_of_zeros` — a real exponential polynomial `∑_{j<n} c_j e^{v_j x}`
  with `n` strictly increasing exponents that vanishes at `n` distinct points has all
  coefficients zero.  (Equivalently: a nonzero exponential polynomial with `n` exponents has
  at most `n − 1` real zeros.)
* `RLHF.exp_sample_uniqueness_general` — consequently two mass vectors on the same `n` known
  distinct levels are equal as soon as their exponential sums agree at `n` distinct
  temperatures.
* `RLHF.spectral_rigidity_sampled_general` — the RLHF audit statement: with `n` known
  candidate reward levels, `n` arbitrary distinct inverse temperatures determine the reward
  spectrum.

Combined with `RLHF.prony_three_samples_insufficient_spectra`, the picture for the sampling
question is complete in the known-level case, and provably different when the levels are
unknown.
-/

open RLHF

open Finset






open RLHF in
theorem solution:
    ∀ (n : ℕ) (v c t : Fin n → ℝ), StrictMono v → StrictMono t →
      (∀ i, ∑ j, c j * Real.exp (v j * t i) = 0) → ∀ j, c j = 0 := by
  intro n
  induction n with
  | zero => intro _ _ _ _ _ _ j; exact j.elim0
  | succ n ih =>
    intro v c t hv ht h
    -- the shifted polynomial `g x = e^{-v₀ x} f x`
    set g : ℝ → ℝ := fun x => ∑ j, c j * Real.exp ((v j - v 0) * x) with hgdef
    set G : ℝ → ℝ := fun x => ∑ j, c j * (v j - v 0) * Real.exp ((v j - v 0) * x) with hGdef
    have hgderiv : ∀ x, HasDerivAt g (G x) x := fun x =>
      hasDerivAt_expPoly c (fun j => v j - v 0) x
    have hgzero : ∀ i, g (t i) = 0 := by
      intro i
      have hfac : ∀ j, c j * Real.exp ((v j - v 0) * t i)
          = Real.exp (-(v 0) * t i) * (c j * Real.exp (v j * t i)) := by
        intro j
        have hexp : Real.exp ((v j - v 0) * t i)
            = Real.exp (-(v 0) * t i) * Real.exp (v j * t i) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hexp]
        ring
      rw [hgdef]
      simp only
      rw [Finset.sum_congr rfl (fun j _ => hfac j), ← Finset.mul_sum, h i, mul_zero]
    -- Rolle on each consecutive pair of zeros
    have hrolle : ∀ i : Fin n, ∃ s ∈ Set.Ioo (t i.castSucc) (t i.succ), G s = 0 := by
      intro i
      have hlt : t i.castSucc < t i.succ := ht (Fin.castSucc_lt_succ (i := i))
      refine exists_hasDerivAt_eq_zero hlt ?_ ?_ (fun x _ => hgderiv x)
      · exact (fun x _ => (hgderiv x).continuousAt.continuousWithinAt)
      · rw [hgzero i.castSucc, hgzero i.succ]
    choose s hs hsG using hrolle
    have hsmono : StrictMono s := by
      intro i i' hii
      have h1 : s i < t i.succ := (hs i).2
      have h2 : t i'.castSucc < s i' := (hs i').1
      have h3 : t i.succ ≤ t i'.castSucc := by
        refine ht.monotone ?_
        rw [Fin.le_def]
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      linarith
    -- apply the inductive hypothesis to the derivative
    have hv' : StrictMono (fun j : Fin n => v j.succ - v 0) := by
      intro j k hjk
      have : v j.succ < v k.succ := hv (Fin.succ_lt_succ_iff.mpr hjk)
      simpa using this
    have hzeros : ∀ i : Fin n,
        ∑ j : Fin n, (c j.succ * (v j.succ - v 0)) * Real.exp ((v j.succ - v 0) * s i) = 0 := by
      intro i
      have hG := hsG i
      rw [hGdef] at hG
      simp only at hG
      rw [Fin.sum_univ_succ] at hG
      simpa using hG
    have hc' := ih (fun j : Fin n => v j.succ - v 0) (fun j => c j.succ * (v j.succ - v 0)) s
      hv' hsmono hzeros
    have hcsucc : ∀ j : Fin n, c j.succ = 0 := by
      intro j
      have hpos : 0 < v j.succ - v 0 := by
        have : v 0 < v j.succ := hv (by
          rw [Fin.lt_def]
          simp only [Fin.val_succ, Fin.val_zero]
          omega)
        linarith
      rcases mul_eq_zero.mp (hc' j) with h1 | h1
      · exact h1
      · exact absurd h1 (ne_of_gt hpos)
    have hc0 : c 0 = 0 := by
      have h0 := h 0
      rw [Fin.sum_univ_succ] at h0
      have hzero : ∑ j : Fin n, c j.succ * Real.exp (v j.succ * t 0) = 0 := by
        refine Finset.sum_eq_zero (fun j _ => ?_)
        rw [hcsucc j, zero_mul]
      rw [hzero, add_zero] at h0
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact h1
      · exact absurd h1 (Real.exp_ne_zero _)
    intro j
    refine Fin.cases ?_ ?_ j
    · exact hc0
    · exact hcsucc
