-- Prove2me | Theorems.Thm_AlmostLossless_exists_quadratic_rate_scanScheme
-- name    : AlmostLossless.exists_quadratic_rate_scanScheme
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T14:16:31.71446+00:00
-- url     : https://prove2.me/theorems/6e1094ca-087c-4f4f-86ec-c6fb0bb4472f
-- title:
--   The rate–determinism trade-off, quantified.
-- statement:
--   **The rate–determinism trade-off, quantified.**  For every typical set `T`
--   of a finite source there is a prime `p ≤ 2|T|²` and an explicit inner-product
--   hash scheme over `ZMod p` whose scan code is honest, decodes every typical word
--   correctly, and costs exactly `|T|` hash evaluations, while transmitting one of
--   only `p + 1` symbols.
--
--   Against the information-theoretic optimum `|T|` symbols
--   (`epsilon_pigeonhole_iff`), the constructive scheme pays a squaring — the
--   birthday penalty of pairwise-independent hashing — and nothing more.
--
--   ```lean
--   theorem AlmostLossless.exists_quadratic_rate_scanScheme(T : Finset S) (hT : T.Nonempty) :
--       ∃ p : ℕ, p.Prime ∧ T.card ^ 2 < p ∧ p ≤ 2 * T.card ^ 2 ∧
--         ∃ (a : Fin (Fintype.card S) → ZMod p)
--           (P : ScanScheme S (Fin (Fintype.card S) → ZMod p) (ZMod p)),
--           P.typical = T ∧ Honest (P.code a) ∧ (∀ s ∈ T, Correct (P.code a) s) ∧
--           (∀ m : ZMod p, P.decodeCost a m = T.card) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Logic/AlmostLossless/Derandomisation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Logic/AlmostLossless/Derandomisation.lean#L84

-- Thm stub generated from Logic/AlmostLossless/Derandomisation.lean
import Mathlib
import Definitions.Def_Logic_AlmostLossless_Core
import Definitions.Def_Logic_AlmostLossless_Instances
import Definitions.Def_Logic_AlmostLossless_Scheme

/-!
# Derandomisation: from Monte Carlo to a deterministic zero-failure compressor

The Monte-Carlo scheme of `Logic.AlmostLossless.Scheme` fails with probability
`≤ ε + |T|(|T|-1)/|M|` over the random seed.  The probabilistic method converts
this into a *deterministic* statement: as soon as `|M| > |T|(|T|-1)` some seed
hashes the whole typical set injectively, and then the compressor never fails on
a typical word at all.  The random number generator is only a proof device; it
can be dispensed with.

The price is the **birthday penalty**: a 2-universal family needs a range of
size about `|T|²`, whereas the exact `ε`-pigeonhole characterisation
(`AlmostLossless.epsilon_pigeonhole_iff`) says `|T|` symbols suffice
information-theoretically.  Bertrand's postulate lets us pin this down:

> `AlmostLossless.exists_quadratic_rate_scanScheme` — for every finite source
> alphabet and every typical set `T` there is a prime `p ≤ 2|T|²` and an
> explicit inner-product hash such that the induced scan code is honest, decodes
> **every** typical word correctly, uses only `p + 1 ≤ 2|T|² + 1` codeword
> symbols and decodes in exactly `|T|` hash evaluations.

So the constructive, checksum-free, never-silently-wrong compressor costs at
most *twice the square* of the information-theoretic alphabet size — a factor
`2` in rate, in exchange for an explicit decoder.
-/

open AlmostLossless

open Finset

/-! ## Pulling a hash family back along an embedding -/


/-! ## The deterministic compressor -/

variable {S : Type*} [Fintype S] [DecidableEq S]



/-! ## Quadratic rate via Bertrand's postulate -/

theorem AlmostLossless.exists_quadratic_rate_scanScheme(T : Finset S) (hT : T.Nonempty) :
    ∃ p : ℕ, p.Prime ∧ T.card ^ 2 < p ∧ p ≤ 2 * T.card ^ 2 ∧
      ∃ (a : Fin (Fintype.card S) → ZMod p)
        (P : ScanScheme S (Fin (Fintype.card S) → ZMod p) (ZMod p)),
        P.typical = T ∧ Honest (P.code a) ∧ (∀ s ∈ T, Correct (P.code a) s) ∧
        (∀ m : ZMod p, P.decodeCost a m = T.card) := by sorry
