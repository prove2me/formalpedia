-- Prove2me | Theorems.Thm_Round10_rootCount_prod
-- name    : Round10.rootCount_prod
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:49:04.400445+00:00
-- url     : https://prove2.me/theorems/ed996dad-eebe-40f1-84fb-ad71e5b1b88e
-- title:
--   Root counts are multiplicative over direct products: the CRT-separability of the
-- statement:
--   Root counts are multiplicative over direct products: the CRT-separability of the
--   witness family.
--
--   ```lean
--   theorem Round10.rootCount_prod(G H : Type*) [Group G] [Group H] (k : ℕ) :
--       rootCount (G × H) k = rootCount G k * rootCount H k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/Round10Closures/TraceLemma.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/Round10Closures/TraceLemma.lean#L45

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

theorem Round10.rootCount_prod(G H : Type*) [Group G] [Group H] (k : ℕ) :
    rootCount (G × H) k = rootCount G k * rootCount H k := by sorry
