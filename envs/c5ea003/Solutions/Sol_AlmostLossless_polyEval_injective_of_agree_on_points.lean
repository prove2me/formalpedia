-- Prove2me | solution 1 for AlmostLossless.polyEval_injective_of_agree_on_points
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:05:24.688296+00:00
-- url     : https://prove2.me/submissions/7d522f2d-3978-44c7-9851-7d79621cacb0

-- Sol generated from Bridges/AlmostLosslessPolyFamily.lean
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












/-! ## A concrete instance with explicit figures -/






open AlmostLossless in
theorem solution{n : ℕ} (pts : Fin n → ZMod p)
    (hinj : Function.Injective pts) (c c' : Fin n → ZMod p)
    (h : ∀ j, ∑ i, c i * pts j ^ (i : ℕ) = ∑ i, c' i * pts j ^ (i : ℕ)) :
    c = c' := by
  have hdet : (Matrix.vandermonde pts).det ≠ 0 :=
    Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  have hmul : (Matrix.vandermonde pts).mulVec (c - c') = 0 := by
    funext j
    have hj := h j
    simp only [Matrix.mulVec, Matrix.vandermonde, dotProduct, Pi.sub_apply, Pi.zero_apply,
      Matrix.of_apply, mul_sub]
    rw [Finset.sum_sub_distrib]
    simp_rw [mul_comm]
    rw [hj, sub_self]
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hdet hmul)
