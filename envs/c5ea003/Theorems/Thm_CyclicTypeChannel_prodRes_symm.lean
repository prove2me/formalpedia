-- Prove2me | Theorems.Thm_CyclicTypeChannel_prodRes_symm
-- name    : CyclicTypeChannel.prodRes_symm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:27:42.592951+00:00
-- url     : https://prove2.me/theorems/68e7192d-1ae1-4f62-9cb9-6ef8b2009fdd
-- title:
--   The residue of the product is symmetric too.
-- statement:
--   The residue of the product is symmetric too.
--
--   ```lean
--   theorem CyclicTypeChannel.prodRes_symm(n : ℕ) (a b : ℕ) : prodRes n (a, b) = prodRes n (b, a) := by sorry
--
--
--
--
--
--   /-! ## 4. Base-two logarithms of the numerals that occur -/
--
--
--
--
--
--
--
--
--
--
--
--
--
--
--
--
--
--
--
--
--   /-! ## 5. Faithfulness of the exponent model, and the exact `φ`-law for `H(T)` -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannel.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannel.lean#L326

-- Thm stub generated from Shared/CyclicTypeChannel.lean
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

theorem CyclicTypeChannel.prodRes_symm(n : ℕ) (a b : ℕ) : prodRes n (a, b) = prodRes n (b, a) := by sorry
