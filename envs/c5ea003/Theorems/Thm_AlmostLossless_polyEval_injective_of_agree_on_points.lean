-- Prove2me | Theorems.Thm_AlmostLossless_polyEval_injective_of_agree_on_points
-- name    : AlmostLossless.polyEval_injective_of_agree_on_points
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:07:14.72049+00:00
-- url     : https://prove2.me/theorems/169e5679-6fba-48de-b7cc-96271067526c
-- title:
--   Interpolation, counting form (sub-conjecture B1).
-- statement:
--   **Interpolation, counting form (sub-conjecture B1).**  Two coefficient
--   vectors of length `T+1` that agree at `T+1` distinct points are equal: the
--   evaluation map is injective because the Vandermonde determinant of distinct
--   nodes is nonzero.
--
--   ```lean
--   theorem AlmostLossless.polyEval_injective_of_agree_on_points{n : ℕ} (pts : Fin n → ZMod p)
--       (hinj : Function.Injective pts) (c c' : Fin n → ZMod p)
--       (h : ∀ j, ∑ i, c i * pts j ^ (i : ℕ) = ∑ i, c' i * pts j ^ (i : ℕ)) :
--       c = c' := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AlmostLosslessPolyFamily.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AlmostLosslessPolyFamily.lean#L57

-- Thm stub generated from Bridges/AlmostLosslessPolyFamily.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessLinearHash
import Definitions.Def_Bridges_AlmostLosslessPolyFamily
import Definitions.Def_Bridges_AlmostLosslessTwiseIndependent
/-
Copyright (c) 2025 Non-Archimedean Information Theory Project. All rights reserved.

# Almost-Lossless Compression XIV: A Short-Key `T`-wise Independent Family

## Bridge: Vandermonde determinants (linear algebra) ↔ higher independence
##         (probability) ↔ list decoding (coding theory)

`AlmostLosslessTwiseIndependent` proves that `(T+1)`-wise independence turns the
linear list-decoding gain `δ + |l|/(T·M)` into the exponential
`δ + (|l|/M)^T`, but its only witness (`fullFamily_indepT`) uses **all**
functions, i.e. `M^{|α|}` keys — exponentially long advice.  Conjecture B of the
previous cycle asked for the same independence from a *short* key.

This file settles Conjecture B (and its sub-conjecture B1) for the degree-`T`
polynomial family over a prime field:

  `h_c(x) = c₀ + c₁x + ⋯ + c_T x^T  (mod p)`,  keyed by `c ∈ (ZMod p)^{T+1}`.

* `polyEval_injective_of_agree_on_points` (**B1**) — the interpolation lemma, in
  the counting form needed here: two coefficient vectors that agree at `T+1`
  distinct points are equal.  It is proved from `Matrix.det_vandermonde_ne_zero_iff`,
  so no polynomial-degree bookkeeping is needed.
* `card_poly_constrained_le` — hence at most `p` keys make the polynomial take
  the same value at `x` as at all `T` points of `s`: the constraint pins the key
  down to its common value.
* `polyHash_indepT` — **the deliverable**: `IndepT (polyHash p T) T` with only
  `K = p^{T+1}` keys, i.e. `(T+1)·log₂ p` bits of advice.
* `exists_poly_list_scheme_exponential` — the resulting compressor: list-`T`
  decoding of any codebook with failure probability `≤ δ + (|l|/p)^T`.
* `concrete_poly_list_scheme` — a fully numeric instance: source `ZMod 101`,
  a 10-element codebook, `T = 3`, key space `101⁴ ≈ 10⁸` (27 bits of advice
  instead of the `101¹⁰¹` keys of the full family), failure probability
  `≤ 1/100 + 1/1000`, list length `≤ 3`.
* `poly_key_exponentially_shorter` — the separation from `fullFamily`: for
  `T + 1 < p` the polynomial key space `p^{T+1}` is strictly smaller than the
  `p^p` keys of the full family, and the gap is exponential in `p`.

## Impact: short_key_twise_independence, vandermonde_derandomization
-/


open Finset BigOperators NonArchInfoTheory

open AlmostLossless


variable (p T : ℕ) [Fact p.Prime]

theorem AlmostLossless.polyEval_injective_of_agree_on_points{n : ℕ} (pts : Fin n → ZMod p)
    (hinj : Function.Injective pts) (c c' : Fin n → ZMod p)
    (h : ∀ j, ∑ i, c i * pts j ^ (i : ℕ) = ∑ i, c' i * pts j ^ (i : ℕ)) :
    c = c' := by sorry
