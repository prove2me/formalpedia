-- Prove2me | solution 1 for Catalog.Probability.SeedRec.PRNG.card_compressible_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T13:04:44.07235+00:00
-- url     : https://prove2.me/submissions/228d02ee-de43-4a4d-b83d-608498b540b0

-- Sol generated from Probability/PRNGSeedRecovery.lean
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












open Catalog.Probability.SeedRec in
omit [Fintype α] in
theorem solution(g : PRNG S α) (n : ℕ) :
    (g.compressible n).card ≤ Fintype.card S := by
  simpa [PRNG.compressible, Finset.card_univ] using
    Finset.card_image_le (s := (Finset.univ : Finset S)) (f := g.pref n)
