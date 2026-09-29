-- Prove2me | solution 1 for Cryptography.TernaryReversible.singleCoordinate_classification_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:12:47.99761+00:00
-- url     : https://prove2.me/submissions/745d2b73-2ede-4dc9-9c22-5257d9da8e77

-- Sol generated from Cryptography/TernaryReversible/General.lean
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core
import Definitions.Def_Cryptography_TernaryReversible_General
import Theorems.Thm_Cryptography_TernaryReversible_cycleBijectiveA_of_decoder3
import Theorems.Thm_Cryptography_TernaryReversible_twistRule_selfDecoder

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








/-- A rule using both its middle and its right cell is not a single coordinate followed
by a permutation. -/
theorem not_singleCoordinatePermA_of_MR {g : A → A → A → A} (hm : DependsMiddleA g)
    (hr : DependsRightA g) : ¬ SingleCoordinatePermA g := by
  rintro ⟨σ, rfl | rfl | rfl⟩
  · obtain ⟨a, b, b', c, hne⟩ := hm; exact hne rfl
  · obtain ⟨a, b, c, c', hne⟩ := hr; exact hne rfl
  · obtain ⟨a, b, b', c, hne⟩ := hm; exact hne rfl



/-- Over a subsingleton alphabet every rule is (trivially) a single coordinate followed
by a permutation. -/
theorem singleCoordinatePermA_of_subsingleton [Subsingleton A] (g : A → A → A → A) :
    SingleCoordinatePermA g := by
  refine ⟨Equiv.refl A, Or.inl ?_⟩
  funext a b c
  exact Subsingleton.elim _ _

/-! ## Alphabets with at least three letters: the claim always fails -/

variable [DecidableEq A]


variable {x₀ x₁ x₂ : A}





/-- Hence it is bijective on every nonempty finite cycle. -/
theorem twistRule_cycleBijectiveA [Fintype A] (h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂) :
    CycleBijectiveA (twistRule x₀ x₁ x₂) :=
  cycleBijectiveA_of_decoder3 _ _ (twistRule_selfDecoder h₁ h₂)

/-- The conditional transposition uses its middle cell. -/
theorem twistRule_dependsMiddle (h₁₂ : x₁ ≠ x₂) : DependsMiddleA (twistRule x₀ x₁ x₂) := by
  refine ⟨x₀, x₁, x₂, x₀, ?_⟩
  show (if x₀ = x₀ then Equiv.swap x₁ x₂ x₁ else x₁)
      ≠ (if x₀ = x₀ then Equiv.swap x₁ x₂ x₂ else x₂)
  rw [if_pos rfl, if_pos rfl, Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact h₁₂.symm

/-- The conditional transposition uses its right cell. -/
theorem twistRule_dependsRight (h₁ : x₀ ≠ x₁) (h₁₂ : x₁ ≠ x₂) :
    DependsRightA (twistRule x₀ x₁ x₂) := by
  refine ⟨x₀, x₁, x₀, x₁, ?_⟩
  show (if x₀ = x₀ then Equiv.swap x₁ x₂ x₁ else x₁) ≠ (if x₁ = x₀ then Equiv.swap x₁ x₂ x₁ else x₁)
  rw [if_pos rfl, if_neg (Ne.symm h₁), Equiv.swap_apply_left]
  exact h₁₂.symm

/-- **The claim fails over every alphabet with at least three letters.** -/
theorem claim_fails_of_three_elements [Fintype A] (h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂)
    (h₁₂ : x₁ ≠ x₂) :
    ¬ (∀ g : A → A → A → A, CycleBijectiveA g → SingleCoordinatePermA g) := by
  intro hall
  exact not_singleCoordinatePermA_of_MR (twistRule_dependsMiddle h₁₂)
    (twistRule_dependsRight h₁ h₁₂)
    (hall _ (twistRule_cycleBijectiveA h₁ h₂))

/-! ## The binary alphabet: the claim is true -/



set_option maxRecDepth 100000 in
/-- **Exhaustive verification over the 256 binary rules**: bijectivity on the cycles of
length `1, 2, 3, 4` already forces the single-coordinate form.  (Length `≤ 3` does not:
twenty binary rules pass that weaker test.) -/
theorem binary_bijUpTo4_classification :
    ∀ g : Fin 2 → Fin 2 → Fin 2 → Fin 2, BijUpTo4 g → SingleCoordinatePermA g := by
  decide

/-- **Binary classification.** Over the binary alphabet the claim under test is true. -/
theorem binary_classification (g : Fin 2 → Fin 2 → Fin 2 → Fin 2) (hg : CycleBijectiveA g) :
    SingleCoordinatePermA g :=
  binary_bijUpTo4_classification g
    ⟨hg 1 one_pos, hg 2 (by norm_num), hg 3 (by norm_num), hg 4 (by norm_num)⟩

/-! ## The dichotomy -/



open Cryptography.TernaryReversible in
theorem solution(q : ℕ) :
    (∀ g : Fin q → Fin q → Fin q → Fin q, CycleBijectiveA g → SingleCoordinatePermA g)
      ↔ q ≤ 2 := by
  constructor
  · intro hall
    by_contra hq
    push_neg at hq
    have h0 : (0 : ℕ) < q := by omega
    have h1 : (1 : ℕ) < q := by omega
    have h2 : (2 : ℕ) < q := by omega
    exact claim_fails_of_three_elements (x₀ := (⟨0, h0⟩ : Fin q)) (x₁ := ⟨1, h1⟩) (x₂ := ⟨2, h2⟩)
      (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) hall
  · intro hq g _
    interval_cases q
    · exact singleCoordinatePermA_of_subsingleton g
    · exact singleCoordinatePermA_of_subsingleton g
    · exact binary_classification g ‹_›
