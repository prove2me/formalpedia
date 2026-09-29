-- Prove2me | solution 1 for CyclicTypeChannel.uEnt_eq_shannon
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:31:02.723746+00:00
-- url     : https://prove2.me/submissions/29496294-66e2-4312-8a48-16e9d720382f

-- Sol generated from Shared/CyclicTypeChannel.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_fiber_card_pos
import Theorems.Thm_CyclicTypeChannel_sum_fiber_card
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
theorem solution(hs : s.Nonempty) (g : α → β) :
    uEnt s g = ∑ v ∈ s.image g,
      -((#{x ∈ s | g x = v} : ℝ) / s.card) *
        Real.logb 2 ((#{x ∈ s | g x = v} : ℝ) / s.card) := by
  classical
  have hN : (0 : ℝ) < s.card := by exact_mod_cast card_pos.2 hs
  have hA : ∑ a ∈ s, Real.logb 2 (#{x ∈ s | g x = g a} : ℝ)
      = ∑ v ∈ s.image g, (#{x ∈ s | g x = v} : ℝ) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ) := by
    rw [Finset.sum_comp (fun v : β => Real.logb 2 (#{x ∈ s | g x = v} : ℝ)) g]
    simp [nsmul_eq_mul]
  have hcard : ∑ v ∈ s.image g, ((#{x ∈ s | g x = v} : ℝ)) = (s.card : ℝ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (sum_fiber_card s g)
  have hsplit : ∀ v ∈ s.image g,
      -((#{x ∈ s | g x = v} : ℝ) / s.card) *
        Real.logb 2 ((#{x ∈ s | g x = v} : ℝ) / s.card)
      = ((#{x ∈ s | g x = v} : ℝ) / s.card) * Real.logb 2 (s.card : ℝ)
        - ((#{x ∈ s | g x = v} : ℝ) / s.card) *
            Real.logb 2 (#{x ∈ s | g x = v} : ℝ) := by
    intro v hv
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
    have hc : (0 : ℝ) < (#{x ∈ s | g x = g a} : ℝ) := by
      exact_mod_cast fiber_card_pos ha
    rw [Real.logb_div (ne_of_gt hc) (ne_of_gt hN)]
    ring
  have h2 : (∑ v ∈ s.image g,
        (#{x ∈ s | g x = v} : ℝ) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ)) / s.card
      = ∑ v ∈ s.image g,
        ((#{x ∈ s | g x = v} : ℝ) / s.card) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [uEnt, hA, Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib, ← Finset.sum_mul,
    ← Finset.sum_div, hcard, h2, div_self (ne_of_gt hN), one_mul]
