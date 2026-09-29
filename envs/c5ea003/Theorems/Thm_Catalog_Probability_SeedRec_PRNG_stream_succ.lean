-- Prove2me | Theorems.Thm_Catalog_Probability_SeedRec_PRNG_stream_succ
-- name    : Catalog.Probability.SeedRec.PRNG.stream_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:04:59.757096+00:00
-- url     : https://prove2.me/theorems/a40d971a-bcef-4809-9950-a4da2cb604cb
-- title:
--   Stream succ
-- statement:
--   Formal statement of `Catalog.Probability.SeedRec.PRNG.stream_succ` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Probability.SeedRec.PRNG.stream_succ(g : PRNG S α) (s : S) (t : ℕ) :
--       g.stream s (t + 1) = g.stream (g.step s) t := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/PRNGSeedRecovery.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/PRNGSeedRecovery.lean#L56

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

theorem Catalog.Probability.SeedRec.PRNG.stream_succ(g : PRNG S α) (s : S) (t : ℕ) :
    g.stream s (t + 1) = g.stream (g.step s) t := by sorry
