-- Prove2me | solution 1 for Novelty.TraceProfile.card_factorSet_prime
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:28:12.748829+00:00
-- url     : https://prove2.me/submissions/d1a7c6db-1482-4043-a41b-f03d61be9048

-- Sol generated from Novelty/TraceProfileFactorInvisible.lean
import Mathlib
import Definitions.Def_Novelty_TraceProfileFactorInvisible
import Definitions.Def_Novelty_TraceProfileTraceSet
/-
# TRACEPROFILE III — factor invisible, trace visible: the exact information contrast

Phase A research file (Novelty domain), Paper 50 / Experiment 385.

The experiment measured, for semiprimes `N = p q` and moduli `m`,

* `I(p mod m ; N mod m) ≈ 0` for **every** `m` (the "zero block"), against
* `I(s mod m ; N mod m) ≈ 1` bit for every odd prime `m`, where `s = p + q`.

This file proves the exact combinatorial content of both halves over a prime
field `F_q`, in the counting form of mutual information (a random variable pair is
information-free exactly when its joint counts factor as a product).

## Main results

* `card_factorSet_prime` — **factor invisibility**: the set of residues a factor of
  a nonzero `N` can occupy is *all* of `F_q^×`; the residue of `N` excludes no
  candidate factor residue.  Zero bits.
* `card_fiber_cofactor` — each candidate factor residue has exactly one completion.
* `factor_indep_of_product` — **`I(p mod q ; N mod q) = 0` exactly**: over the
  uniform model on pairs of units, the events `{x = a}` and `{x y = b}` satisfy the
  product rule for all `a`, `b`.
* `trace_not_indep_of_product` — **the trace is different**: the analogous product
  rule *fails* for the trace at `q = 5`, so `I(s mod q ; N mod q) > 0`.
* `traceSet_card_lt_factorSet_card` — the quantitative contrast: for `q ≥ 5` the
  trace is confined to strictly fewer residues than the factor, `≈ q/2` versus
  `q - 1`.
* `trace_bit_versus_factor_bits` — one bit for the trace, zero for the factor,
  in the same normalisation: `2 * |traceSet| ≤ |factorSet| + 2 = q + 1`.
-/


open Novelty.TraceProfile

open Finset


@[simp] theorem mem_factorSet {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {N x : R} : x ∈ factorSet N ↔ ∃ y : R, x * y = N := by
  simp [factorSet, factorPairs, Prod.exists]


variable {q : ℕ} [hq : Fact (Nat.Prime q)]









variable {q : ℕ} [hq : Fact (Nat.Prime q)]





open Novelty.TraceProfile in
theorem solution(N : ZMod q) (hN : N ≠ 0) :
    factorSet N = univ.filter (fun x : ZMod q => x ≠ 0) ∧ (factorSet N).card = q - 1 := by
  have hset : factorSet N = univ.filter (fun x : ZMod q => x ≠ 0) := by
    ext x
    simp only [mem_factorSet, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨y, hxy⟩
      rintro rfl
      rw [zero_mul] at hxy
      exact hN hxy.symm
    · intro hx
      exact ⟨N * x⁻¹, by field_simp⟩
  refine ⟨hset, ?_⟩
  rw [hset]
  have hAe : (univ.filter (fun x : ZMod q => x ≠ 0)) = univ.erase (0 : ZMod q) := by
    ext x; simp [Finset.mem_erase]
  rw [hAe, Finset.card_erase_of_mem (mem_univ 0), Finset.card_univ, ZMod.card]
