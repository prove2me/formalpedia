-- Prove2me | Theorems.Thm_ChaitinBerry_chaitin_incompressible_infinite
-- name    : ChaitinBerry.chaitin_incompressible_infinite
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:19:39.70305+00:00
-- url     : https://prove2.me/theorems/4734bf5d-21c7-4e9b-b493-38bb494bfd7a
-- title:
--   Incompressible numbers are not sporadic but infinitely many: for every threshold the
-- statement:
--   Incompressible numbers are not sporadic but **infinitely many**: for every threshold the
--   set of numbers whose complexity exceeds it is infinite.  A single incompressible number would
--   not suffice to defeat compression; here compression fails everywhere.
--
--   ```lean
--   theorem ChaitinBerry.chaitin_incompressible_infinite(enc : ℕ → ℕ) (hinj : Injective enc) (n : ℕ) :
--       {x | n < K enc x}.Infinite := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/ChaitinBerry.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/ChaitinBerry.lean#L108

-- Thm stub generated from Logic/ChaitinBerry.lean
import Mathlib
import Definitions.Def_Logic_ChaitinBerry
/-
# Chaitin's Incompleteness and the Berry Paradox: The Counting Face of Self-Reference

Where `Logic.LucasPenroseGodel` develops the *logical* face of self-referential
limitation (a sentence that outruns its own provability), this file develops its
*information-theoretic* face, following Chaitin and the Berry paradox.

The Berry paradox — "the least number not nameable in fewer than twenty syllables",
itself a description of about a dozen syllables — becomes, once "nameable" is replaced by
an injective description code, an exact counting theorem: there are strictly fewer short
descriptions than the numbers they would have to name, so some numbers are
**incompressible**.  This is the combinatorial kernel of Chaitin's incompleteness theorem.

## Set-up

Fix any *injective* encoding `enc : ℕ → ℕ`, thought of as assigning to each number a
unique description (its code).  The **descriptive complexity** of `x` is the number of
binary digits of its code,
  `K x := Nat.size (enc x)`,
the length of the shortest binary word representing `enc x`.

## Main results

* `size_lt_iff_lt_pow` — the elementary bridge `Nat.size y ≤ n ↔ y < 2 ^ n`: numbers with
  at most `n` bits are exactly those below `2 ^ n`.
* `berry_pigeonhole` — the **finite Berry paradox**: among any `2 ^ n + 1` numbers, at
  least one has complexity exceeding `n`.  You cannot compress `2 ^ n + 1` distinct objects
  into descriptions of at most `n` bits.
* `chaitin_incompressible` — **Chaitin's incompressibility theorem**: complexity is
  unbounded; for every `n` there is a number whose complexity exceeds `n`.  No encoding
  makes all numbers simultaneously short.
* `chaitin_incompressible_infinite` — strengthening: incompressible numbers are not merely
  present but *infinitely many*; for every threshold the set of numbers of complexity above
  it is infinite.
* `no_universal_compressor` — the impossibility of a **universal short compressor**: there
  is no encoding under which every number has complexity below a fixed global bound.
* `berry_undefinable` — the Berry sentence is self-defeating: there is no `n` such that
  "the numbers of complexity `> n`" is empty, so "the least number of complexity `> n`" is
  always a genuine (and short-to-specify) object, reproducing the paradox constructively.

-- !-- Lab Notes -- !--
Hypothesis (Stage 1): the Berry paradox and Chaitin's theorem are the *counting shadow* of
  the diagonal argument — replace "provability" by "compressibility" and "there is a true
  unprovable sentence" becomes "there is an incompressible number", derivable by pure
  pigeonhole rather than fixed-point self-reference.
Experiment (Stage 2): we modelled descriptive complexity as the bit-length `Nat.size (enc x)`
  of an injective code and proved incompressibility by comparing the `2 ^ n` short codes with
  the infinitely (or `2 ^ n + 1`) many numbers requiring them.
Analysis (Stage 3): the single load-bearing arithmetic fact is `Nat.size_le`
  (`size y ≤ n ↔ y < 2 ^ n`); everything else is `Finset` cardinality (finite Berry) or the
  pigeonhole that an injection `ℕ ↪ Fin (2 ^ n)` cannot exist (unbounded Chaitin).
Critique (Stage 4): injectivity of `enc` is essential and non-vacuous — the identity code
  `enc = id` already satisfies every hypothesis, so the theorems have genuine content and are
  not vacuously true; dropping injectivity makes `chaitin_incompressible` false (a constant
  code compresses everything to complexity `0`).
Synthesis (Stage 5): `chaitin_incompressible` (some number is incompressible) is the exact
  analogue of `FormalSystem.godel_true` (some truth is unprovable); both witness that a
  finitely-described system cannot capture all of an infinite domain.
-/

open Function

open ChaitinBerry

theorem ChaitinBerry.chaitin_incompressible_infinite(enc : ℕ → ℕ) (hinj : Injective enc) (n : ℕ) :
    {x | n < K enc x}.Infinite := by sorry
