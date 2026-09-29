-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_PRNG_card_compressible_le
-- name    : Catalog.Probability.SeedRec.PRNG.card_compressible_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:04:13.032428+00:00
-- url     : https://prove2.me/theorems/5581a63f-d809-4757-a80d-e8ebf3fb307e
-- title:
--   Pigeonhole ceiling for seed compression.
-- statement:
--   **Pigeonhole ceiling for seed compression.** At most `|S|` words of any
--   length are reproducible from a seed.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.PRNG.card_compressible_le(g : PRNG S α) (n : ℕ) :
--       (g.compressible n).card ≤ Fintype.card S := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGSeedRecovery.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGSeedRecovery.lean#L86

-- Thm stub generated from Probability/PRNGSeedRecovery.lean
import Mathlib
import Definitions.Def_Probability_PRNGSeedRecovery

/-!
# Seed-compressibility: a generic framework for PRNG detection and seed recovery

This file develops the abstract theory behind the question *"is this file PRNG
output, and if so, what was the seed?"*.

A deterministic pseudorandom generator is a pair `(step, out)` on a state space
`S` producing a symbol stream in `α`.  A finite word `x : Fin n → α` is
**seed-compressible** for the generator if some seed reproduces it exactly:
this is the falsifiability gate of the research programme (the decompressed
output must equal the file bit-for-bit).

Main contents.

* `PRNG`, `PRNG.stream`, `PRNG.pref` — generator, its output stream, its
  length-`n` prefix (the "file" it would produce).
* `SeedCompressible` — the exact-reproduction predicate.
* `PRNG.compressible` — the finite set of seed-compressible words.
* `PRNG.card_compressible_le` — **pigeonhole ceiling**: at most `|S|` of the
  `|α|ⁿ` words are seed-compressible.
* `PRNG.exists_not_seedCompressible` — hence, as soon as `|S| < |α|ⁿ`, some
  file is *not* seed-compressible: seed compression cannot beat the counting
  bound.
* `PRNG.density_le` — the density of seed-compressible files, i.e. the false
  positive rate of an ideal detector on uniformly random data.
* `PRNG.decode`, `PRNG.decode_pref` — the seed-recovery decoder and its exact
  round-trip guarantee.
* `PRNG.stream_eq_of_pref_eq_of_injective` — **extrapolation soundness**: if the
  prefix map is injective, agreement on the observed window forces agreement
  forever.
-/

open Catalog.Probability.SeedRec

universe u v


variable {S : Type u} {α : Type v}



@[simp] theorem PRNG.stream_zero (g : PRNG S α) (s : S) : g.stream s 0 = g.out s := rfl






variable [Fintype S] [Fintype α] [DecidableEq α]



omit [Fintype α] in

theorem Catalog.Probability.SeedRec.PRNG.card_compressible_le(g : PRNG S α) (n : ℕ) :
    (g.compressible n).card ≤ Fintype.card S := by sorry
