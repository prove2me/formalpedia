-- Prove2me | Theorems.Thm_Round11_card_fix_field
-- name    : Round11.card_fix_field
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:29:00.330913+00:00
-- url     : https://prove2.me/theorems/16a95402-e015-402e-98d3-c647394b27da
-- title:
--   In a finite field, `c · x = x` has `#F` solutions if `c = 1` and one otherwise.
-- statement:
--   In a finite field, `c · x = x` has `#F` solutions if `c = 1` and one otherwise.
--
--   ```lean
--   theorem Round11.card_fix_field{F : Type*} [Field F] [Fintype F] [DecidableEq F] (c : F) :
--       Fintype.card {x : F // c * x = x} = if c = 1 then Fintype.card F else 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/Round11OrbitCountSeal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/Round11OrbitCountSeal.lean#L43

-- Thm stub generated from Combinatorics/Round11OrbitCountSeal.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
/-
# Round-11 Closures, Part II: the orbit-count (GROUPOID) identity, via Burnside

Formal companion to the round-11 negative-results synthesis
(`29_Round11_Closures.md`, hypothesis **GROUPOID**).

The paper records the orbit-count ("homotopy cardinality") identity
```
C(b) = 1 + φ(N)/ord_N(b) + (p-1)/ord_p(b) + (q-1)/ord_q(b)
```
for the action of `⟨b⟩` on `ℤ/N`, `N = p·q`, and observes that it re-sums exactly
the data that factoring already requires.  Here it is *proved*, in the
division-free form
```
C(b) · n = n + (p-1)·(n/ord_p b) + (q-1)·(n/ord_q b) + (p-1)(q-1),
n = ord_N(b) = lcm (ord_p b) (ord_q b),
```
where `C(b)` is the honest number of orbits of the cyclic group `⟨b⟩ ≤ (ℤ/N)ˣ`
acting on `ℤ/N` (`Round11.groupoid_orbit_identity`).  Note `φ(N) = (p-1)(q-1)`
and the `(p-1)(q-1)` term is exactly the single free orbit `φ(N)/ord_N(b) · n`
… divided out; see `Round11.groupoid_orbit_identity_totient` for the statement
written with `Nat.totient`.

The bridge to Part I is the observation that the **cycle-index fingerprint is a
fixed-point count**:
```
#{x ∈ ℤ/N : b^k x = x} = gcd (b^k - 1) N = F(k)
```
(`Round11.card_fix_eq_fpr`), so Burnside's lemma turns the orbit count into the
average of the fingerprint over a full period.  This is the precise sense in
which the topological/groupoid re-encoding "re-sums the same sealed data": the
orbit count is a linear functional of the very fingerprint whose Möbius spectrum
Part I showed to be supported at the order scale.
-/

open Round11

open Finset MulAction

/-! ## Fixed-point counts -/

theorem Round11.card_fix_field{F : Type*} [Field F] [Fintype F] [DecidableEq F] (c : F) :
    Fintype.card {x : F // c * x = x} = if c = 1 then Fintype.card F else 1 := by sorry
