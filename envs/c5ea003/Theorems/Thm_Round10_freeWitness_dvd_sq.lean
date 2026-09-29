-- Prove2me | Theorems.Thm_Round10_freeWitness_dvd_sq
-- name    : Round10.freeWitness_dvd_sq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:49:11.745511+00:00
-- url     : https://prove2.me/theorems/4c7a390b-571a-40bc-950c-6d390152b636
-- title:
--   Every free witness divides `k ^ 2`: the witness carries at most `2 log k` bits,
-- statement:
--   Every free witness divides `k ^ 2`: the witness carries at most `2 log k` bits,
--   independently of the size of `N`.  (Barrier-4 bookkeeping: a single exponent leaks a
--   bounded amount of information.)
--
--   ```lean
--   theorem Round10.freeWitness_dvd_sq(p q k : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : Nat.Coprime p q) :
--       freeWitness (p * q) k ∣ k ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/TraceLemma.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/TraceLemma.lean#L93

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

theorem Round10.freeWitness_dvd_sq(p q k : ℕ) [Fact p.Prime] [Fact q.Prime] (hpq : Nat.Coprime p q) :
    freeWitness (p * q) k ∣ k ^ 2 := by sorry
