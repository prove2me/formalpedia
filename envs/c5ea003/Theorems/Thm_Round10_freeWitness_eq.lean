-- Prove2me | Theorems.Thm_Round10_freeWitness_eq
-- name    : Round10.freeWitness_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:49:14.967168+00:00
-- url     : https://prove2.me/theorems/154f5d06-3fef-4476-bd69-b5f14f078715
-- title:
--   The trace lemma.
-- statement:
--   **The trace lemma.**  For a semiprime modulus `N = p * q` with `p`, `q` coprime primes,
--   the number of `k`-th roots of unity modulo `N` is `gcd(p-1, k) * gcd(q-1, k)`.
--
--   Every free witness of the family therefore factors through the two gcd-residue
--   coordinates; no exponent `k` sees anything else about the factorisation.
--
--   ```lean
--   theorem Round10.freeWitness_eq(p q k : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : Nat.Coprime p q) :
--       freeWitness (p * q) k = (p - 1).gcd k * (q - 1).gcd k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/TraceLemma.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/TraceLemma.lean#L75

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



/-! ## The free-witness family -/

theorem Round10.freeWitness_eq(p q k : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : Nat.Coprime p q) :
    freeWitness (p * q) k = (p - 1).gcd k * (q - 1).gcd k := by sorry
