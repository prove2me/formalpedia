-- Prove2me | solution 1 for AlmostLossless.card_poly_constrained_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:07:03.318148+00:00
-- url     : https://prove2.me/submissions/c4ed7221-9b4d-4c22-9c63-bc0e8fc28687

-- Sol generated from Bridges/AlmostLosslessPolyFamily.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessLinearHash
import Definitions.Def_Bridges_AlmostLosslessPolyFamily
import Definitions.Def_Bridges_AlmostLosslessTwiseIndependent
import Theorems.Thm_AlmostLossless_polyEval_injective_of_agree_on_points
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
theorem solution(x : ZMod p) (s : Finset (ZMod p))
    (hs : s.card = T) (hx : x ∉ s) :
    (Finset.univ.filter
        (fun c : Fin (T + 1) → ZMod p => ∀ y ∈ s, polyEval p T c y = polyEval p T c x)).card
      ≤ p := by
  classical
  -- enumerate the `T+1` distinct constraint points
  have hcard : (insert x s).card = T + 1 := by
    rw [Finset.card_insert_of_notMem hx, hs]
  set e : ↥(insert x s) ≃ Fin (T + 1) := Finset.equivFinOfCardEq hcard with he
  set pts : Fin (T + 1) → ZMod p := fun j => ((e.symm j : ↥(insert x s)) : ZMod p) with hpts
  have hptsinj : Function.Injective pts := by
    intro j₁ j₂ hj
    have : e.symm j₁ = e.symm j₂ := Subtype.ext hj
    exact e.symm.injective this
  have hptsmem : ∀ j, pts j ∈ insert x s := fun j => (e.symm j).2
  -- the map `c ↦ polyEval c x` is injective on the constrained set
  have hinj : Set.InjOn (fun c : Fin (T + 1) → ZMod p => polyEval p T c x)
      ↑(Finset.univ.filter
        (fun c : Fin (T + 1) → ZMod p => ∀ y ∈ s, polyEval p T c y = polyEval p T c x)) := by
    intro c hc c' hc' hval
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hc hc'
    have hvalx : polyEval p T c x = polyEval p T c' x := hval
    refine polyEval_injective_of_agree_on_points p pts hptsinj c c' ?_
    intro j
    rcases Finset.mem_insert.mp (hptsmem j) with hj | hj
    · rw [hj]; exact hvalx
    · have h1 : polyEval p T c (pts j) = polyEval p T c x := hc _ hj
      have h2 : polyEval p T c' (pts j) = polyEval p T c' x := hc' _ hj
      have : polyEval p T c (pts j) = polyEval p T c' (pts j) := by
        rw [h1, h2, hvalx]
      exact this
  have hmaps : ∀ c ∈ Finset.univ.filter
      (fun c : Fin (T + 1) → ZMod p => ∀ y ∈ s, polyEval p T c y = polyEval p T c x),
      polyEval p T c x ∈ (Finset.univ : Finset (ZMod p)) := fun c _ => Finset.mem_univ _
  have hle := Finset.card_le_card_of_injOn _ hmaps hinj
  rwa [Finset.card_univ, ZMod.card] at hle
