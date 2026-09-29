-- Prove2me | Theorems.Thm_AsymmetricExponent_card_revealing
-- name    : AsymmetricExponent.card_revealing
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T02:32:25.926507+00:00
-- url     : https://prove2.me/theorems/be40f608-bea9-4cc3-a363-c6ff9e1e574e
-- title:
--   The reveal density law.
-- statement:
--   **The reveal density law.** Adding the two sides, the gcd variant
--   `gcd(a^(N-1) - 1, N)` returns a factor for exactly
--
--     `g·(q-1) + g·(p-1) - 2g²`
--
--   of the `φ(N) = (p-1)(q-1)` units — a fraction `≈ g/(p-1) + g/(q-1)`, the
--   measured `g/p + g/q` law.  In particular the reveal density is governed by the
--   Euler gap alone, and drops to the negligible `(p-1) + (q-1) - 2` when `g = 1`.
--
--   ```lean
--   theorem AsymmetricExponent.card_revealing[Fact p.Prime] [Fact q.Prime] :
--       Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ //
--           v.1 ^ (p * q - 1) = 1 ∧ ¬ v.2 ^ (p * q - 1) = 1}
--         + Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ //
--           v.2 ^ (p * q - 1) = 1 ∧ ¬ v.1 ^ (p * q - 1) = 1}
--         = eulerGap p q * (q - 1) + eulerGap p q * (p - 1) - 2 * (eulerGap p q) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/AsymmetricExponent/RevealDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/AsymmetricExponent/RevealDensity.lean#L137

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

theorem AsymmetricExponent.card_revealing[Fact p.Prime] [Fact q.Prime] :
    Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ //
        v.1 ^ (p * q - 1) = 1 ∧ ¬ v.2 ^ (p * q - 1) = 1}
      + Nat.card {v : (ZMod p)ˣ × (ZMod q)ˣ //
        v.2 ^ (p * q - 1) = 1 ∧ ¬ v.1 ^ (p * q - 1) = 1}
      = eulerGap p q * (q - 1) + eulerGap p q * (p - 1) - 2 * (eulerGap p q) ^ 2 := by sorry
