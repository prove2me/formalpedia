-- Prove2me | solution 1 for CyclicTypeChannel.uEnt_of_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:30:42.612509+00:00
-- url     : https://prove2.me/submissions/ea5a91a0-17e9-40a2-b986-8463432dcea5

-- Sol generated from Shared/CyclicTypeChannel.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
/-
# The cyclic splitting-type channel

A self-contained, formally verified account of the *splitting-type channel* of a
cyclic field extension.

For a prime `f` the Galois group of `ℚ(ζ_f)/ℚ` is `(ℤ/f)ˣ ≅ C n` with `n = f - 1`.
Writing an unramified prime `p` as `g ^ a` for a fixed generator `g`, the residue
degree (= the order of the Frobenius `p mod f`) is

  `T(p) = ord_f(p) = n / gcd(a, n)`.

This file develops:

* a general finite (counting) Shannon-entropy framework `uEnt`, its conditional
  version `condEnt` and the mutual information `mutInfo`;
* the general structural facts: the Shannon form of `uEnt`, non-negativity, the
  `log₂ |s|` cap, and the *data-processing* inequality for deterministic
  coarsenings;
* the group-theoretic grounding: `orderOf (g ^ a) = ordType n a` for a generator
  `g` of a cyclic group of order `n`, and the exact type-count law
  `#{a : ordType n a = d} = φ d`;
* exact closed-form evaluations of the type channel and of the *type-pair
  channel* of a semiprime for `n = 2, 4, 6, 10, 12, 16`, culminating in the
  headline fact that the pair channel of `C₄` and `C₆` carries strictly more
  than one bit.
-/

open CyclicTypeChannel

open Finset

/-! ## 1. A counting Shannon-entropy framework -/

variable {α β γ : Type*}





variable [DecidableEq β] {s : Finset α} {g : α → β}












/-! ## 2. The splitting type of a cyclic Frobenius -/







/-! ## 3. The type channel and the semiprime type-pair channel -/




















/-! ## 4. Base-two logarithms of the numerals that occur -/




















/-! ## 5. Faithfulness of the exponent model, and the exact `φ`-law for `H(T)` -/









open CyclicTypeChannel in
lemma solution(h : s.card ≤ 1) (g : α → β) : uEnt s g = 0 := by
  classical
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · rw [Finset.card_eq_zero] at h0
    simp [uEnt, h0]
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
    simp [uEnt, Finset.filter_singleton]
