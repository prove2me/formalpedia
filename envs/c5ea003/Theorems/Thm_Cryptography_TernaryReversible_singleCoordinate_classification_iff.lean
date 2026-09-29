-- Prove2me | Theorems.Thm_Cryptography_TernaryReversible_singleCoordinate_classification_iff
-- name    : Cryptography.TernaryReversible.singleCoordinate_classification_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:46:29.777499+00:00
-- url     : https://prove2.me/theorems/b29c6359-1295-45d3-8745-52671f4c9168
-- title:
--   The size-two dichotomy.
-- statement:
--   **The size-two dichotomy.** For the alphabet `Fin q`, every rule that is bijective on
--   all nonempty finite cycles is a single coordinate followed by a permutation **iff**
--   `q ≤ 2`.  Radius-one reversibility is rigid exactly up to two letters.
--
--   ```lean
--   theorem Cryptography.TernaryReversible.singleCoordinate_classification_iff(q : ℕ) :
--       (∀ g : Fin q → Fin q → Fin q → Fin q, CycleBijectiveA g → SingleCoordinatePermA g)
--         ↔ q ≤ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/TernaryReversible/General.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/TernaryReversible/General.lean#L218

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









/-! ## The binary alphabet: the claim is true -/





/-! ## The dichotomy -/

theorem Cryptography.TernaryReversible.singleCoordinate_classification_iff(q : ℕ) :
    (∀ g : Fin q → Fin q → Fin q → Fin q, CycleBijectiveA g → SingleCoordinatePermA g)
      ↔ q ≤ 2 := by sorry
