-- Prove2me | Definitions.Def_Probability_PRNGSeedRecovery
-- name    : Probability_PRNGSeedRecovery
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:25:29.064103+00:00
-- url     : https://prove2.me/theorems/34e2bf30-39a5-470e-bb4c-557e7635dccd
-- title:
--   Aether Catalog definitions — Probability_PRNGSeedRecovery
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.PRNGSeedRecovery`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/PRNGSeedRecovery.lean by skeleton subtraction
import Mathlib

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

namespace Catalog.Probability.SeedRec

universe u v

/-- A deterministic pseudorandom generator: a state transition together with an
output function. -/
structure PRNG (S : Type u) (α : Type v) where
  /-- The state transition of the generator. -/
  step : S → S
  /-- The output (extraction) function. -/
  out : S → α

variable {S : Type u} {α : Type v}

/-- The infinite output stream of the generator started at seed `s`. -/
def PRNG.stream (g : PRNG S α) (s : S) (t : ℕ) : α := g.out (g.step^[t] s)

/-- The length-`n` prefix produced from seed `s` — the "file" the generator writes. -/
def PRNG.pref (g : PRNG S α) (n : ℕ) (s : S) : Fin n → α := fun i => g.stream s i

@[simp] theorem PRNG.stream_zero (g : PRNG S α) (s : S) : g.stream s 0 = g.out s := rfl



/-- `x` is seed-compressible for `g` if some seed reproduces it exactly. -/
def SeedCompressible (g : PRNG S α) (n : ℕ) (x : Fin n → α) : Prop :=
  ∃ s : S, g.pref n s = x


section Finite

variable [Fintype S] [Fintype α] [DecidableEq α]

/-- The finite set of all seed-compressible words of length `n`. -/
def PRNG.compressible (g : PRNG S α) (n : ℕ) : Finset (Fin n → α) :=
  Finset.univ.image (g.pref n)





end Finite

/-- Seed recovery: a decoder that produces a seed reproducing the observed file. -/
noncomputable def PRNG.decode (g : PRNG S α) {n : ℕ} {x : Fin n → α}
    (h : SeedCompressible g n x) : S := h.choose




end Catalog.Probability.SeedRec


