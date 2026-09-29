-- Prove2me | solution 1 for PRNGSeed.linRec_taps_unique_of_span
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:54:48.170862+00:00
-- url     : https://prove2.me/submissions/eca9f57e-7e6e-4394-89d1-996f38c22231

-- Sol generated from MachineLearning/PRNGSeedRecoveryLFSR.lean
import Mathlib
import Definitions.Def_MachineLearning_PRNGSeedRecoveryLFSR
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Seed Recovery for Linear Feedback Shift Registers

This module formalises the mathematical core of *seed recovery* for the LFSR
family of pseudo-random generators, the first half of the "detect PRNG output
and replace the file by its seed" programme (see
`MachineLearning.PRNGCompressionBound` for the counting-side limits).

An LFSR of order `L` over a commutative ring `F` with tap vector
`c : Fin L → F` produces a stream `x : ℕ → F` obeying

  `x (n + L) = ∑ i < L, c i * x (n + i)`.

## Main results

* `lfsrRun` — the generator: run the register from an explicit seed.
* `lfsrRun_isLinRec`, `lfsrRun_of_lt` — the generator does what it claims.
* `IsLinRec.ext_of_agree` — **rigidity**: two streams with the same taps that
  agree on one window of length `L` agree forever.
* `IsLinRec.seed_recovery` — **the falsifiability gate**: any stream obeying the
  recurrence is *exactly* reproduced by re-running the register from its own
  first `L` symbols.  Nothing beyond the seed has to be stored.
* `linRec_taps_unique_of_span` — **Berlekamp–Massey uniqueness**: if the first
  `L` state windows span `F^L`, the tap vector is uniquely determined by the
  stream, so seed recovery has a unique answer.
* `hankel_span_of_taps_unique` — the converse over a field: tap uniqueness
  forces the windows to span.  Spanning is therefore *exactly* the right
  nondegeneracy condition.

## Application keywords

LFSR, linear recurrence, Berlekamp–Massey, seed recovery, PRNG fingerprinting,
stream compression
-/


open Finset

open PRNGSeed


variable {F : Type*} [CommRing F]



variable {L : ℕ} {c init : Fin L → F}








/-! ### Periodic data is seed-compressible -/









variable {F : Type*} [Field F] {L : ℕ} {x : ℕ → F}




@[simp] lemma dotL_apply (e v : Fin L → F) : dotL e v = ∑ i : Fin L, e i * v i := rfl

lemma dotL_eq_zero_iff {e : Fin L → F} : (∀ v : Fin L → F, dotL e v = 0) ↔ e = 0 := by
  constructor
  · intro h
    funext j
    have hj := h (Pi.single j 1)
    rw [dotL_apply, Finset.sum_eq_single j] at hj
    · simpa using hj
    · intro b _ hb; simp [hb]
    · intro hj'; exact absurd (Finset.mem_univ j) hj'
  · rintro rfl v; simp







open PRNGSeed in
theorem solution{c d : Fin L → F} (hspan : windowSpan x L = ⊤)
    (hc : IsLinRec L c x) (hd : IsLinRec L d x) : c = d := by
  set e : Fin L → F := fun i => c i - d i with he
  have hker : ∀ n : ℕ, dotL e (window x L n) = 0 := by
    intro n
    have h := (hc n).symm.trans (hd n)
    simp only [dotL_apply, window, he, sub_mul, Finset.sum_sub_distrib]
    rw [h, sub_self]
  have hzero : ∀ v : Fin L → F, dotL e v = 0 := by
    intro v
    have hv : v ∈ windowSpan x L := by rw [hspan]; trivial
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hv
    · rintro w ⟨n, rfl⟩; exact hker n
    · simp
    · intro a b _ _ ha hb; simp only [map_add, ha, hb, add_zero]
    · intro a b _ hb; simp only [map_smul, hb, smul_zero]
  have : e = 0 := dotL_eq_zero_iff.mp hzero
  funext i
  have := congrFun this i
  simp only [he, Pi.zero_apply, sub_eq_zero] at this
  exact this
