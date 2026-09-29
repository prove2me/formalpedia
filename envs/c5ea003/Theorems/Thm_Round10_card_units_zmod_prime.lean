-- Prove2me | Theorems.Thm_Round10_card_units_zmod_prime
-- name    : Round10.card_units_zmod_prime
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:48:21.92045+00:00
-- url     : https://prove2.me/theorems/f2f8e7a5-7348-45dc-a101-cb2895287041
-- title:
--   Card units zmod prime
-- statement:
--   Formal statement of `Round10.card_units_zmod_prime` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Round10.card_units_zmod_prime(p : ℕ) [Fact p.Prime] : Nat.card (ZMod p)ˣ = p - 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/TraceLemma.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/TraceLemma.lean#L65

-- Thm stub generated from Geometry/Round10Closures/TraceLemma.lean
import Mathlib
import Definitions.Def_Geometry_Round10Closures_TraceLemma
/-
Round-10 Closures — Part I: the trace lemma for free witnesses.

The "free witness" of exponent `k` attached to a semiprime `N = p * q` is the
number of `k`-th roots of unity in `(ZMod N)ˣ`.  The folklore formula

    R_k(N) = gcd(k, p-1) * gcd(k, q-1)

is the arithmetic content of the *trace lemma*: every numeric witness of this
family factors through the pair of gcd-residue coordinates
`(gcd(k,p-1), gcd(k,q-1))`, and through nothing else.

This file gives a complete, sorry-free proof of that formula, together with the
structural lemmas it rests on (root counting in cyclic groups, transport along
group isomorphisms, multiplicativity over direct products, CRT for `ZMod`).
-/

open Round10

open scoped Classical

/-! ## Counting roots of unity -/






/-! ## The unit group of a semiprime modulus -/

theorem Round10.card_units_zmod_prime(p : ℕ) [Fact p.Prime] : Nat.card (ZMod p)ˣ = p - 1 := by sorry
