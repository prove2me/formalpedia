-- Prove2me | solution 1 for AlmostLossless.polyHash_indepT
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:19:30.470982+00:00
-- url     : https://prove2.me/submissions/4a54e647-b5e6-4646-b4da-0d3c16ec03e7

-- Sol generated from Bridges/AlmostLosslessPolyFamily.lean
import Mathlib
import Definitions.Def_Bridges_AlmostLosslessLinearHash
import Definitions.Def_Bridges_AlmostLosslessPolyFamily
import Definitions.Def_Bridges_AlmostLosslessTwiseIndependent
import Theorems.Thm_AlmostLossless_card_poly_constrained_le
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







theorem polyHash_eq_iff {k : Fin (p ^ (T + 1))} {x y : ZMod p} :
    polyHash p T k x = polyHash p T k y ↔
      polyEval p T (polyKey p T k) x = polyEval p T (polyKey p T k) y := by
  unfold polyHash
  rw [Fin.mk.injEq]
  exact ⟨fun h => ZMod.val_injective p h, fun h => by rw [h]⟩





/-! ## A concrete instance with explicit figures -/






open AlmostLossless in
theorem solution: IndepT (polyHash p T) T := by
  classical
  intro x s hs hx
  set e := polyKey p T with he
  -- transport the count along the key indexing
  have hbij : (Finset.univ.filter
        (fun k => ∀ y ∈ s, polyHash p T k y = polyHash p T k x)).card
      = (Finset.univ.filter (fun c : Fin (T + 1) → ZMod p =>
          ∀ y ∈ s, polyEval p T c y = polyEval p T c x)).card := by
    refine Finset.card_bij (fun k _ => e k) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      intro y hy
      exact (polyHash_eq_iff p T).mp (hk y hy)
    · intro k₁ _ k₂ _ h
      exact e.injective h
    · intro c hc
      refine ⟨e.symm c, ?_, by simp [he]⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      intro y hy
      rw [polyHash_eq_iff]
      simpa [he] using hc y hy
  rw [hbij]
  have hcount : ((Finset.univ.filter (fun c : Fin (T + 1) → ZMod p =>
      ∀ y ∈ s, polyEval p T c y = polyEval p T c x)).card : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast card_poly_constrained_le p T x s hs hx
  have hppos : (0 : ℝ) ≤ (p : ℝ) ^ T := by positivity
  calc ((Finset.univ.filter (fun c : Fin (T + 1) → ZMod p =>
        ∀ y ∈ s, polyEval p T c y = polyEval p T c x)).card : ℝ) * (p : ℝ) ^ T
      ≤ (p : ℝ) * (p : ℝ) ^ T := mul_le_mul_of_nonneg_right hcount hppos
    _ = ((p ^ (T + 1) : ℕ) : ℝ) := by push_cast; ring
