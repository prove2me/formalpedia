-- Prove2me | Theorems.Thm_Round10_rootCount_of_isCyclic
-- name    : Round10.rootCount_of_isCyclic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:49:02.732035+00:00
-- url     : https://prove2.me/theorems/c794b9ca-e656-459e-b02d-6b32aea97e46
-- title:
--   Cyclic root count.
-- statement:
--   **Cyclic root count.** In a finite cyclic group of order `n` there are exactly
--   `gcd(n, k)` solutions of `x ^ k = 1`.
--
--   ```lean
--   theorem Round10.rootCount_of_isCyclic(G : Type*) [CommGroup G] [IsCyclic G] [Finite G] (k : ℕ) :
--       rootCount G k = (Nat.card G).gcd k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/TraceLemma.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/TraceLemma.lean#L33

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

theorem Round10.rootCount_of_isCyclic(G : Type*) [CommGroup G] [IsCyclic G] [Finite G] (k : ℕ) :
    rootCount G k = (Nat.card G).gcd k := by sorry
