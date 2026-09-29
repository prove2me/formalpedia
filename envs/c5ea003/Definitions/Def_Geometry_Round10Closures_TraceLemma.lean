-- Prove2me | Definitions.Def_Geometry_Round10Closures_TraceLemma
-- name    : Geometry_Round10Closures_TraceLemma
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:54:34.589016+00:00
-- url     : https://prove2.me/theorems/55311e04-8db8-4251-91cf-2e1b74f185ee
-- title:
--   Aether Catalog definitions — Geometry_Round10Closures_TraceLemma
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.Round10Closures.TraceLemma`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/Round10Closures/TraceLemma.lean by skeleton subtraction
import Mathlib
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

namespace Round10

open scoped Classical

/-! ## Counting roots of unity -/

/-- `rootCount G k` is the number of solutions of `x ^ k = 1` in the group `G`. -/
noncomputable def rootCount (G : Type*) [Group G] (k : ℕ) : ℕ :=
  Nat.card {x : G // x ^ k = 1}





/-! ## The unit group of a semiprime modulus -/

/-- Chinese remainder theorem at the level of unit groups. -/
noncomputable def unitsMulEquivProd {m n : ℕ} (h : Nat.Coprime m n) :
    (ZMod (m * n))ˣ ≃* (ZMod m)ˣ × (ZMod n)ˣ :=
  (Units.mapEquiv (ZMod.chineseRemainder h).toMulEquiv).trans MulEquiv.prodUnits


/-! ## The free-witness family -/

/-- The free witness `R_k(N)` of a semiprime `N = p * q`, defined intrinsically as the
number of `k`-th roots of unity modulo `N`. -/
noncomputable def freeWitness (N k : ℕ) : ℕ := rootCount (ZMod N)ˣ k





end Round10


