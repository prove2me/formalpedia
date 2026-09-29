-- Prove2me | solution 1 for CyclicTypeChannel.uEnt_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:32:51.269882+00:00
-- url     : https://prove2.me/submissions/32d482b2-846d-491a-9c4a-b6328790d6ed

-- Sol generated from Shared/CyclicTypeChannel.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_fiber_card_pos
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
theorem solution[DecidableEq γ] (s : Finset α) (g : α → β) (h : β → γ) :
    uEnt s (h ∘ g) ≤ uEnt s g := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [uEnt]
  have hN : (0 : ℝ) < s.card := by exact_mod_cast card_pos.2 hs
  have hterm : ∀ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ)
      ≤ Real.logb 2 (#{x ∈ s | (h ∘ g) x = (h ∘ g) a} : ℝ) := by
    intro a ha
    have hsub : {x ∈ s | g x = g a} ⊆ {x ∈ s | (h ∘ g) x = (h ∘ g) a} := by
      intro x hx
      simp only [mem_filter] at hx ⊢
      exact ⟨hx.1, by simp [Function.comp, hx.2]⟩
    have hc : (0 : ℝ) < (#{x ∈ s | g x = g a} : ℝ) := by
      exact_mod_cast fiber_card_pos ha
    have hle : (#{x ∈ s | g x = g a} : ℝ) ≤ (#{x ∈ s | (h ∘ g) x = (h ∘ g) a} : ℝ) := by
      exact_mod_cast card_le_card hsub
    exact Real.logb_le_logb_of_le (by norm_num) hc hle
  have hsum := Finset.sum_le_sum hterm
  have hdiv : (∑ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ)) / s.card
      ≤ (∑ a ∈ s, Real.logb 2 (#{x ∈ s | (h ∘ g) x = (h ∘ g) a} : ℝ)) / s.card := by
    gcongr
  simp only [uEnt]
  linarith
