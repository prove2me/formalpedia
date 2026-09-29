-- Prove2me | solution 1 for Novelty.TraceProfile.factor_indep_of_product
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T02:37:29.392977+00:00
-- url     : https://prove2.me/submissions/286eb1d0-ceae-4243-9432-4968c6ac9193

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




variable {q : ℕ} [hq : Fact (Nat.Prime q)]




theorem card_unitPairs : (unitPairs q).card = (q - 1) * (q - 1) := by
  have h : unitPairs q
      = (univ.filter (fun x : ZMod q => x ≠ 0)) ×ˢ (univ.filter (fun x : ZMod q => x ≠ 0)) := by
    ext z; simp [unitPairs, mem_product]
  have hA : (univ.filter (fun x : ZMod q => x ≠ 0)).card = q - 1 := by
    have hAe : (univ.filter (fun x : ZMod q => x ≠ 0)) = univ.erase (0 : ZMod q) := by
      ext x; simp [Finset.mem_erase]
    rw [hAe, Finset.card_erase_of_mem (mem_univ 0), Finset.card_univ, ZMod.card]
  rw [h, Finset.card_product, hA]





variable {q : ℕ} [hq : Fact (Nat.Prime q)]





open Novelty.TraceProfile in
theorem solution(a b : ZMod q) (ha : a ≠ 0) (hb : b ≠ 0) :
    ((unitPairs q).filter (fun z => z.1 = a ∧ z.1 * z.2 = b)).card * (unitPairs q).card
      = ((unitPairs q).filter (fun z => z.1 = a)).card
        * ((unitPairs q).filter (fun z => z.1 * z.2 = b)).card := by
  have hA : (univ.filter (fun x : ZMod q => x ≠ 0)).card = q - 1 := by
    have hAe : (univ.filter (fun x : ZMod q => x ≠ 0)) = univ.erase (0 : ZMod q) := by
      ext x; simp [Finset.mem_erase]
    rw [hAe, Finset.card_erase_of_mem (mem_univ 0), Finset.card_univ, ZMod.card]
  -- the joint event is a single point
  have hjoint : ((unitPairs q).filter (fun z => z.1 = a ∧ z.1 * z.2 = b)).card = 1 := by
    rw [Finset.card_eq_one]
    refine ⟨(a, a⁻¹ * b), ?_⟩
    ext ⟨z1, z2⟩
    simp only [unitPairs, Finset.filter_filter, mem_filter, mem_univ, true_and, mem_singleton,
      Prod.mk.injEq]
    constructor
    · rintro ⟨⟨-, hz2⟩, rfl, hprod⟩
      refine ⟨rfl, ?_⟩
      field_simp
      linear_combination hprod
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨ha, mul_ne_zero (inv_ne_zero ha) hb⟩, rfl, by field_simp⟩
  -- the marginal in the factor
  have hmarg1 : ((unitPairs q).filter (fun z => z.1 = a)).card = q - 1 := by
    have : ((unitPairs q).filter (fun z => z.1 = a))
        = ({a} : Finset (ZMod q)) ×ˢ (univ.filter (fun x : ZMod q => x ≠ 0)) := by
      ext z
      simp only [unitPairs, Finset.filter_filter, mem_filter, mem_univ, true_and, mem_product,
        mem_singleton]
      constructor
      · rintro ⟨⟨-, hz2⟩, rfl⟩; exact ⟨rfl, hz2⟩
      · rintro ⟨rfl, hz2⟩; exact ⟨⟨ha, hz2⟩, rfl⟩
    rw [this, Finset.card_product, Finset.card_singleton, hA, one_mul]
  -- the marginal in the product
  have hmarg2 : ((unitPairs q).filter (fun z => z.1 * z.2 = b)).card = q - 1 := by
    have himg : ((unitPairs q).filter (fun z => z.1 * z.2 = b))
        = (univ.filter (fun x : ZMod q => x ≠ 0)).image (fun x => (x, x⁻¹ * b)) := by
      ext ⟨z1, z2⟩
      simp only [unitPairs, Finset.filter_filter, mem_filter, mem_univ, true_and, mem_image,
        Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hz1, hz2⟩, hprod⟩
        refine ⟨z1, hz1, rfl, ?_⟩
        field_simp
        linear_combination -hprod
      · rintro ⟨x, hx, rfl, rfl⟩
        refine ⟨⟨hx, mul_ne_zero (inv_ne_zero hx) hb⟩, ?_⟩
        field_simp
    rw [himg, Finset.card_image_of_injective, hA]
    intro x y hxy
    exact (Prod.ext_iff.1 hxy).1
  rw [hjoint, hmarg1, hmarg2, card_unitPairs, one_mul]
