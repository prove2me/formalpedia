-- Prove2me | Theorems.Thm_Cryptography_TernaryReversible_twistRule_selfDecoder
-- name    : Cryptography.TernaryReversible.twistRule_selfDecoder
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:46:16.306784+00:00
-- url     : https://prove2.me/theorems/8922228c-8e80-4f73-9651-052846eb380a
-- title:
--   Self-decoding.
-- statement:
--   **Self-decoding.** The conditional transposition inverts itself.
--
--   ```lean
--   theorem Cryptography.TernaryReversible.twistRule_selfDecoder(h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂) :
--       ∀ v w x y z, twistRule x₀ x₁ x₂ (twistRule x₀ x₁ x₂ v w x) (twistRule x₀ x₁ x₂ w x y)
--         (twistRule x₀ x₁ x₂ x y z) = x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/TernaryReversible/General.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/TernaryReversible/General.lean#L138

-- Thm stub generated from Cryptography/TernaryReversible/General.lean
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

theorem Cryptography.TernaryReversible.twistRule_selfDecoder(h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂) :
    ∀ v w x y z, twistRule x₀ x₁ x₂ (twistRule x₀ x₁ x₂ v w x) (twistRule x₀ x₁ x₂ w x y)
      (twistRule x₀ x₁ x₂ x y z) = x := by sorry
