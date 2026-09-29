-- Prove2me | solution 1 for AlmostLossless.universal2_key_ge_codes
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:19:31.807344+00:00
-- url     : https://prove2.me/submissions/e65342a4-609e-492c-ba0c-d16296cf4f34

-- Sol generated from Bridges/AlmostLosslessKeySharp.lean
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







variable (p : ℕ) [Fact p.Prime]





open AlmostLossless in
omit [DecidableEq α] in
theorem solution{H : Fin K → α → Fin M} (hU : Universal2 H)
    (hK : 0 < K) (hn : M < Fintype.card α) : M ≤ K := by
  classical
  by_contra hcon
  push_neg at hcon
  -- no two distinct symbols can collide under any key
  have hzero : ∀ x y : α, x ≠ y → ∀ k : Fin K, H k x ≠ H k y := by
    intro x y hxy k hk
    have hmem : k ∈ Finset.univ.filter (fun k => H k x = H k y) := by
      simp [hk]
    have hpos : 1 ≤ (Finset.univ.filter (fun k => H k x = H k y)).card :=
      Finset.card_pos.mpr ⟨k, hmem⟩
    have hboundR := hU x y hxy
    have hposR : (1 : ℝ) ≤ ((Finset.univ.filter (fun k => H k x = H k y)).card : ℝ) := by
      exact_mod_cast hpos
    have hMR : (K : ℝ) < (M : ℝ) := by exact_mod_cast hcon
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
    nlinarith [hboundR, hposR, hMR, hM0]
  -- hence the first hash function is injective
  set k₀ : Fin K := ⟨0, hK⟩ with hk₀
  have hinj : Function.Injective (H k₀) := by
    intro x y hxy
    by_contra hne
    exact hzero x y hne k₀ hxy
  have hcard : Fintype.card α ≤ M := by
    have := Fintype.card_le_of_injective (H k₀) hinj
    rwa [Fintype.card_fin] at this
  omega
