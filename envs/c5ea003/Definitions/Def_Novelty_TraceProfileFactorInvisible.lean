-- Prove2me | Definitions.Def_Novelty_TraceProfileFactorInvisible
-- name    : Novelty_TraceProfileFactorInvisible
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:44:52.300199+00:00
-- url     : https://prove2.me/theorems/2cb7e874-7d6d-4a95-8231-bca9d040da66
-- title:
--   Aether Catalog definitions — Novelty_TraceProfileFactorInvisible
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.TraceProfileFactorInvisible`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/TraceProfileFactorInvisible.lean by skeleton subtraction
import Mathlib
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


namespace Novelty.TraceProfile

open Finset

/-- The set of residues that a *factor* of `N` can occupy. -/
def factorSet {R : Type*} [CommRing R] [Fintype R] [DecidableEq R] (N : R) : Finset R :=
  (factorPairs N).image (fun z => z.1)


section Prime

variable {q : ℕ} [hq : Fact (Nat.Prime q)]



/-- The uniform sample space of the experiment: ordered pairs of nonzero residues
(the residues of the two prime factors). -/
def unitPairs (q : ℕ) [NeZero q] : Finset (ZMod q × ZMod q) :=
  univ.filter (fun z => z.1 ≠ 0 ∧ z.2 ≠ 0)



end Prime


section Contrast

variable {q : ℕ} [hq : Fact (Nat.Prime q)]



end Contrast

end Novelty.TraceProfile


