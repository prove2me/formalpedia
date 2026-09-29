-- Prove2me | solution 1 for PRNGSeed.windowSpan_eq_top_of_taps_unique
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T22:54:49.505335+00:00
-- url     : https://prove2.me/submissions/e2f663e9-0d9f-44fa-85c1-b67a00e18948

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


lemma window_mem_windowSpan (x : ℕ → F) (L n : ℕ) : window x L n ∈ windowSpan x L :=
  Submodule.subset_span ⟨n, rfl⟩


@[simp] lemma dotL_apply (e v : Fin L → F) : dotL e v = ∑ i : Fin L, e i * v i := rfl








open PRNGSeed in
theorem solution{c : Fin L → F} (hc : IsLinRec L c x)
    (huniq : ∀ d : Fin L → F, IsLinRec L d x → d = c) : windowSpan x L = ⊤ := by
  by_contra hne
  obtain ⟨φ, hφ0, hφ⟩ :=
    Submodule.exists_le_ker_of_lt_top (windowSpan x L) (lt_top_iff_ne_top.mpr hne)
  set e : Fin L → F := fun i => φ (Pi.single i 1) with he
  have hφe : ∀ v : Fin L → F, φ v = dotL e v := by
    intro v
    have hv : v = ∑ i : Fin L, v i • (Pi.single i (1 : F) : Fin L → F) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum, dotL_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    simp [he, mul_comm]
  have hene : e ≠ 0 := by
    intro h0
    refine hφ0 (LinearMap.ext fun v => ?_)
    rw [hφe v, dotL_apply, h0]
    simp
  have hker : ∀ n : ℕ, ∑ i : Fin L, e i * x (n + (i : ℕ)) = 0 := by
    intro n
    have hmem := window_mem_windowSpan x L n
    have := hφ hmem
    rw [LinearMap.mem_ker, hφe, dotL_apply] at this
    simpa [window] using this
  have hc' : IsLinRec L (fun i => c i + e i) x := by
    intro n
    simp only [add_mul, Finset.sum_add_distrib, hker n, add_zero]
    exact hc n
  have hde := huniq _ hc'
  have : e = 0 := by
    funext i
    have := congrFun hde i
    simpa using this
  exact hene this
