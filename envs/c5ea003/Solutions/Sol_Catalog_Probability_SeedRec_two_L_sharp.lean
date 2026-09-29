-- Prove2me | solution 1 for Catalog.Probability.SeedRec.two_L_sharp
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:24:13.757263+00:00
-- url     : https://prove2.me/submissions/9786731c-5a86-4445-a6e5-2ffb85f06c00

-- Sol generated from Probability/PRNGTwoLSharpness.lean
import Mathlib
import Definitions.Def_Probability_PRNGBerlekampMassey
import Definitions.Def_Probability_PRNGLFSRDetection
import Definitions.Def_Probability_PRNGSeedRecovery
import Theorems.Thm_Catalog_Probability_SeedRec_lfsr_recurrence
import Theorems.Thm_Catalog_Probability_SeedRec_lfsr_stream_lt

/-!
# Sharpness of the `2L` certificate

`lfsr_stream_determined_by_two_L` says that `2L` matching output symbols certify
an order-`L` seed for ever.  This file shows the constant cannot be improved:
for every order `L ≥ 1` and every nontrivial coefficient ring there are two
order-`L` registers whose outputs agree on `2L - 1` symbols and disagree
immediately afterwards.

The witness is the *impulse* seed `σ = (0, …, 0, 1)` run with two tap vectors:

* zero taps — the stream is the single impulse `0^{L-1} 1 0 0 …`;
* the taps `(1, 0, …, 0)`, i.e. the recurrence `y_{t+L} = y_t` — the stream is
  the periodic impulse train `0^{L-1} 1 0^{L-1} 1 …`.

They first differ at time `2L - 1`.

Main statement: `two_L_sharp`.
-/

open Catalog.Probability.SeedRec

variable {K : Type*} [CommRing K] {L : ℕ} [NeZero L]

/-- With zero taps the register empties: after the seed window the output is `0`. -/
theorem stream_zero_taps (σ : Fin L → K) (t : ℕ) :
    (lfsrPRNG (0 : Fin L → K)).stream σ t = if h : t < L then σ ⟨t, h⟩ else 0 := by
  by_cases ht : t < L
  · rw [dif_pos ht, lfsr_stream_lt _ _ t ht]
  · rw [dif_neg ht]
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + L := ⟨t - L, by omega⟩
    simpa using lfsr_recurrence (0 : Fin L → K) σ t'

/-- The taps `(1, 0, …, 0)` implement the pure delay `y_{t+L} = y_t`. -/
theorem stream_delay_taps (σ : Fin L → K) (t : ℕ) :
    (lfsrPRNG (fun j : Fin L => if (j : ℕ) = 0 then (1 : K) else 0)).stream σ (t + L)
      = (lfsrPRNG (fun j : Fin L => if (j : ℕ) = 0 then (1 : K) else 0)).stream σ t := by
  rw [lfsr_recurrence]
  rw [Finset.sum_eq_single (⟨0, Nat.pos_of_ne_zero (NeZero.ne L)⟩ : Fin L)]
  · simp
  · intro j _ hj
    have : (j : ℕ) ≠ 0 := fun h => hj (Fin.ext h)
    simp [this]
  · intro h
    exact absurd (Finset.mem_univ _) h



open Catalog.Probability.SeedRec in
theorem solution[Nontrivial K] :
    ∃ c c' σ σ' : Fin L → K,
      (∀ t < 2 * L - 1, (lfsrPRNG c).stream σ t = (lfsrPRNG c').stream σ' t) ∧
        (lfsrPRNG c).stream σ (2 * L - 1) ≠ (lfsrPRNG c').stream σ' (2 * L - 1) := by
  have hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
  set e : Fin L → K := fun i => if (i : ℕ) = L - 1 then 1 else 0 with he
  set c1 : Fin L → K := fun j => if (j : ℕ) = 0 then (1 : K) else 0 with hc1
  refine ⟨0, c1, e, e, ?_, ?_⟩
  · intro t ht
    by_cases htL : t < L
    · rw [stream_zero_taps e t, dif_pos htL, lfsr_stream_lt c1 e t htL]
    · obtain ⟨t', rfl⟩ : ∃ t', t = t' + L := ⟨t - L, by omega⟩
      have ht' : t' < L - 1 := by omega
      rw [stream_zero_taps e (t' + L), dif_neg htL, stream_delay_taps e t',
        lfsr_stream_lt c1 e t' (by omega)]
      simp [he, Nat.ne_of_lt ht']
  · have h1 : 2 * L - 1 = (L - 1) + L := by omega
    rw [h1, stream_zero_taps e ((L - 1) + L), dif_neg (by omega), stream_delay_taps e (L - 1),
      lfsr_stream_lt c1 e (L - 1) (by omega)]
    simp [he]
