-- Prove2me | Theorems.Thm_AlmostLossless_universal2_key_ge_codes
-- name    : AlmostLossless.universal2_key_ge_codes
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:09:39.301562+00:00
-- url     : https://prove2.me/theorems/80d80e4d-2d7e-44a4-a86e-43c6f1a3f562
-- title:
--   A 2-universal family that compresses has at least `M` keys.
-- statement:
--   **A 2-universal family that compresses has at least `M` keys.**  If `K < M`
--   then `K/M < 1`, and since the number of keys on which two distinct symbols
--   collide is an integer bounded by `K/M`, it is `0`: every hash function of the
--   family is injective, so the source has at most `M` symbols and nothing is
--   compressed.
--
--   ```lean
--   theorem AlmostLossless.universal2_key_ge_codes{H : Fin K → α → Fin M} (hU : Universal2 H)
--       (hK : 0 < K) (hn : M < Fintype.card α) : M ≤ K := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessKeySharp.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessKeySharp.lean#L48

-- Thm stub generated from Bridges/AlmostLosslessKeySharp.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression XV: The Key Space is at Least as Large as the Code

## Bridge: integrality of a counting bound (combinatorics) ↔ derandomization

`AlmostLosslessKeyBound` proves the pigeonhole bound `K ≥ log_M n` on the number
of keys of a 2-universal family: only *logarithmically* many keys are forced.
Conjecture E of the previous cycle asked whether the truth is polynomial in the
source size.  Second-moment counting cannot answer this — averaging the number
of collisions over keys reproduces exactly the universality hypothesis and gives
a vacuous inequality (see `FUTURE_DIRECTIONS.md`).  What does answer it is
**integrality**: the number of keys on which two fixed symbols collide is a
natural number bounded by `K/M`, so as soon as `K < M` it must be `0`, i.e.
every hash function in the family is injective.

* `universal2_key_ge_codes` — **the sharp bound**: a nonempty 2-universal family
  compressing at all (`M < n`) has at least `M` keys;
* `universal2_key_ge_max` — combined with the pigeonhole bound:
  `K ≥ max(M, log_M n)`;
* `universal2_key_pow_bound` — the resolution of Conjecture E: if the code space
  is a `c`-th root of the source (`n ≤ M^c`) then `n ≤ K^c`, so the key space is
  polynomially large in the source and **no** 2-universal family in that regime
  has `poly(log n)` keys;
* `linHash_key_bound_tight` — the bound is attained: the inner-product family
  has exactly `K = M = p` on a source of `p²` symbols.

So the key-length hierarchy is settled in the compressing regime: `log₂ K` is
between `log₂ M` and `log₂ M` — the encoder's advice must be as long as the
codeword it produces, and the field family shows one codeword's worth of advice
is enough.

## Impact: sharp_key_lower_bound, key_length_equals_codeword_length
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless


variable {α : Type*} [Fintype α] [DecidableEq α] {K M : ℕ}

omit [DecidableEq α] in

theorem AlmostLossless.universal2_key_ge_codes{H : Fin K → α → Fin M} (hU : Universal2 H)
    (hK : 0 < K) (hn : M < Fintype.card α) : M ≤ K := by sorry
