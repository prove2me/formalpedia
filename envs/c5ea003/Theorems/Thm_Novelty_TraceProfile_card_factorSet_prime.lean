-- Prove2me | Theorems.Thm_Novelty_TraceProfile_card_factorSet_prime
-- name    : Novelty.TraceProfile.card_factorSet_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:17:37.029597+00:00
-- url     : https://prove2.me/theorems/88f21120-6326-4535-a7ff-a62b9c58e56e
-- title:
--   Factor invisibility.
-- statement:
--   **Factor invisibility.**  Over a prime field every nonzero residue occurs as the
--   residue of a factor of any nonzero `N`: the public residue `N mod q` rules out no
--   candidate.  The factor residue set has `q - 1` elements — the full unit group.
--
--   ```lean
--   theorem Novelty.TraceProfile.card_factorSet_prime(N : ZMod q) (hN : N ≠ 0) :
--       factorSet N = univ.filter (fun x : ZMod q => x ≠ 0) ∧ (factorSet N).card = q - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/TraceProfileFactorInvisible.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/TraceProfileFactorInvisible.lean#L51

-- Thm stub generated from Novelty/TraceProfileFactorInvisible.lean
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

theorem Novelty.TraceProfile.card_factorSet_prime(N : ZMod q) (hN : N ≠ 0) :
    factorSet N = univ.filter (fun x : ZMod q => x ≠ 0) ∧ (factorSet N).card = q - 1 := by sorry
