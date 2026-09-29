-- Prove2me | Theorems.Thm_AsymmetricExponent_card_left_liars
-- name    : AsymmetricExponent.card_left_liars
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:32:27.712346+00:00
-- url     : https://prove2.me/theorems/74a22dec-9c80-4ff0-9e2c-fdae076f13a9
-- title:
--   Units whose *left* CRT component is a Fermat liar: there are `g·(q-1)`.
-- statement:
--   Units whose *left* CRT component is a Fermat liar: there are `g·(q-1)`.
--
--   ```lean
--   theorem AsymmetricExponent.card_left_liars[Fact p.Prime] [Fact q.Prime] :
--       Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ // v.1 ^ (p * q - 1) = 1}
--         = eulerGap p q * (q - 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AsymmetricExponent/RevealDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AsymmetricExponent/RevealDensity.lean#L57

-- Thm stub generated from Cryptography/AsymmetricExponent/RevealDensity.lean
import Mathlib
import Definitions.Def_Cryptography_AsymmetricExponent_FermatLiars

/-!
# Reveal density of the gcd variant `gcd(a^(N-1) - 1, N)`

The third experimental claim about `Q` concerns its gcd variant: for how many
bases `a` does `gcd(Q(a) - 1, N)` actually return a factor?  The measurement
reported a density tracking `g/p + g/q` with `g = gcd(p-1, q-1)`.  Here that is
proved exactly.

Main results.

* `AsymmetricExponent.gcd_reveal_left` / `gcd_reveal_right` — the arithmetic
  criterion: the gcd returns `p` exactly when `a^(N-1) ≡ 1 (mod p)` while
  `a^(N-1) ≢ 1 (mod q)`, i.e. (by `Core.lean`) when `ord_p(a) ∣ q-1` but
  `ord_q(a) ∤ p-1`.
* `AsymmetricExponent.card_left_liars` — exactly `g·(q-1)` units satisfy the
  left condition.
* `AsymmetricExponent.card_revealing` — the number of revealing units is
  `g·(q-1) + g·(p-1) - 2g²`, i.e. a fraction
  `g/(p-1) + g/(q-1) - 2g²/φ(N)` of all units: the measured `g/p + g/q` law.
-/

open AsymmetricExponent

open scoped Classical

/-! ## The arithmetic criterion -/



/-! ## Counting the revealing bases -/

variable {p q : ℕ}

theorem AsymmetricExponent.card_left_liars[Fact p.Prime] [Fact q.Prime] :
    Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ // v.1 ^ (p * q - 1) = 1}
      = eulerGap p q * (q - 1) := by sorry
