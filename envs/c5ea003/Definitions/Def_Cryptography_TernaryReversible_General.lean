-- Prove2me | Definitions.Def_Cryptography_TernaryReversible_General
-- name    : Cryptography_TernaryReversible_General
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:23:56.873682+00:00
-- url     : https://prove2.me/theorems/5f633294-aae6-4d86-9193-f7db98ca7a9c
-- title:
--   Aether Catalog definitions — Cryptography_TernaryReversible_General
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.TernaryReversible.General`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/TernaryReversible/General.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core

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

namespace Cryptography
namespace TernaryReversible

/-! ## The general framework -/

variable {A : Type}

/-- Global map of a radius-one rule over an arbitrary alphabet. -/
def globalMapA (g : A → A → A → A) {n : ℕ} (s : ZMod n → A) : ZMod n → A :=
  fun i => g (s (i - 1)) (s i) (s (i + 1))

/-- Bijectivity on every nonempty finite cycle, over an arbitrary alphabet. -/
def CycleBijectiveA (g : A → A → A → A) : Prop :=
  ∀ n : ℕ, 0 < n → Function.Bijective (globalMapA (n := n) g)

/-- Single coordinate followed by a permutation, over an arbitrary alphabet. -/
def SingleCoordinatePermA (g : A → A → A → A) : Prop :=
  ∃ σ : Equiv.Perm A, g = (fun a _ _ => σ a) ∨ g = (fun _ b _ => σ b) ∨ g = (fun _ _ c => σ c)

instance decidableSingleCoordinatePermA [Fintype A] [DecidableEq A] (g : A → A → A → A) :
    Decidable (SingleCoordinatePermA g) := by
  unfold SingleCoordinatePermA; infer_instance


/-- `g` genuinely uses its middle argument. -/
def DependsMiddleA (g : A → A → A → A) : Prop := ∃ a b b' c, g a b c ≠ g a b' c

/-- `g` genuinely uses its right argument. -/
def DependsRightA (g : A → A → A → A) : Prop := ∃ a b c c', g a b c ≠ g a b c'





/-! ## Alphabets with at least three letters: the claim always fails -/

variable [DecidableEq A]

/-- The conditional transposition rule: transpose `x₁` and `x₂` in the current cell
exactly when the right neighbour equals `x₀`. -/
def twistRule (x₀ x₁ x₂ : A) : A → A → A → A :=
  fun _ b c => if c = x₀ then Equiv.swap x₁ x₂ b else b

variable {x₀ x₁ x₂ : A}









/-! ## The binary alphabet: the claim is true -/

/-- Bijectivity on the four shortest cycles. -/
def BijUpTo4 (g : A → A → A → A) : Prop :=
  Function.Bijective (globalMapA (n := 1) g) ∧ Function.Bijective (globalMapA (n := 2) g) ∧
    Function.Bijective (globalMapA (n := 3) g) ∧ Function.Bijective (globalMapA (n := 4) g)

instance decidableBijUpTo4 [Fintype A] [DecidableEq A] (g : A → A → A → A) :
    Decidable (BijUpTo4 g) := by
  unfold BijUpTo4; infer_instance



/-! ## The dichotomy -/


end TernaryReversible
end Cryptography


