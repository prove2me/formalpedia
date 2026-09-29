-- Prove2me | solution 1 for Cryptography.TernaryReversible.twistRule_selfDecoder
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:10:25.000635+00:00
-- url     : https://prove2.me/submissions/721eba6e-b219-4ff0-9dbe-c22938414375

-- Sol generated from Cryptography/TernaryReversible/General.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core
import Definitions.Def_Cryptography_TernaryReversible_General

/-!
# The size-two dichotomy for radius-one reversibility

Everything so far concerned the ternary alphabet.  This file identifies **exactly** for
which alphabets the single-coordinate classification claim is true.

For an arbitrary alphabet `A` we consider radius-one rules `g : A → A → A → A` with the
global maps `globalMapA g s i = g (s (i-1)) (s i) (s (i+1))` on the cycle `ZMod n`.

* If `A` has at least three elements `x₀, x₁, x₂` then the **conditional transposition**
  `twistRule x₀ x₁ x₂ a b c = if c = x₀ then (x₁ x₂)·b else b` is an involution on every
  finite cycle — the transposition fixes `x₀`, so the positions carrying `x₀` are visible
  in the output and the twist can be undone — while it uses two cells of its window.
  Hence the claim fails for *every* alphabet of size `≥ 3`; the ternary counterexamples
  of `Refutation.lean` are the smallest instance of a universal phenomenon.
* For the binary alphabet the claim is **true**: bijectivity on the cycles of length
  `1, 2, 3, 4` already forces a rule on `Fin 2` to be a single coordinate followed by a
  permutation (an exhaustive verification over all `2⁸ = 256` binary rules).

The two results combine into `singleCoordinate_classification_iff`: for `A = Fin q` the
classification claim holds **iff** `q ≤ 2`.

## Main results

* `twistRule_involution`, `twistRule_cycleBijectiveA`, `claim_fails_of_three_elements`;
* `binary_classification`;
* `singleCoordinate_classification_iff`.
-/

open Cryptography
open TernaryReversible

/-! ## The general framework -/

variable {A : Type}












/-! ## Alphabets with at least three letters: the claim always fails -/

variable [DecidableEq A]


variable {x₀ x₁ x₂ : A}

/-- The transposition fixes the marker letter `x₀`. -/
theorem swap_fix (h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂) : Equiv.swap x₁ x₂ x₀ = x₀ :=
  Equiv.swap_apply_of_ne_of_ne h₁ h₂

/-- Being equal to the marker letter is invariant under the transposition. -/
theorem swap_eq_marker_iff (h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂) (y : A) :
    Equiv.swap x₁ x₂ y = x₀ ↔ y = x₀ := by
  constructor
  · intro h
    have : Equiv.swap x₁ x₂ y = Equiv.swap x₁ x₂ x₀ := by rw [h, swap_fix h₁ h₂]
    exact (Equiv.swap x₁ x₂).injective this
  · rintro rfl
    exact swap_fix h₁ h₂







/-! ## The binary alphabet: the claim is true -/





/-! ## The dichotomy -/



open Cryptography.TernaryReversible in
theorem solution(h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂) :
    ∀ v w x y z, twistRule x₀ x₁ x₂ (twistRule x₀ x₁ x₂ v w x) (twistRule x₀ x₁ x₂ w x y)
      (twistRule x₀ x₁ x₂ x y z) = x := by
  intro v w x y z
  show (if (if z = x₀ then Equiv.swap x₁ x₂ y else y) = x₀
      then Equiv.swap x₁ x₂ (if y = x₀ then Equiv.swap x₁ x₂ x else x)
      else (if y = x₀ then Equiv.swap x₁ x₂ x else x)) = x
  by_cases hy : y = x₀
  · have hcond : (if z = x₀ then Equiv.swap x₁ x₂ y else y) = x₀ := by
      subst hy; split <;> simp [swap_fix h₁ h₂]
    rw [hcond, if_pos rfl, if_pos hy, Equiv.swap_apply_self]
  · have hcond : ¬ (if z = x₀ then Equiv.swap x₁ x₂ y else y) = x₀ := by
      split
      · rw [swap_eq_marker_iff h₁ h₂]; exact hy
      · exact hy
    rw [if_neg hcond, if_neg hy]
