-- Prove2me | solution 1 for Round11.card_fix_field
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:33:09.44846+00:00
-- url     : https://prove2.me/submissions/58378f78-c6be-4928-80b7-1695da4d1238

-- Sol generated from Combinatorics/Round11OrbitCountSeal.lean
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



/-! ## Counting multiples -/


/-! ## The Burnside average of the fingerprint -/


/-! ## The order of `b` modulo a semiprime -/


/-! ## GROUPOID: the orbit count -/







open Round11 in
theorem solution{F : Type*} [Field F] [Fintype F] [DecidableEq F] (c : F) :
    Fintype.card {x : F // c * x = x} = if c = 1 then Fintype.card F else 1 := by
  split
  · next h => subst h; simp
  · next h =>
      have hiff : ∀ x : F, c * x = x ↔ x = 0 := by
        intro x
        refine ⟨fun hx => ?_, by rintro rfl; simp⟩
        have h0 : (c - 1) * x = 0 := by rw [sub_mul, hx, one_mul, sub_self]
        rcases mul_eq_zero.1 h0 with h1 | h1
        · exact absurd (by linear_combination h1 : c = 1) h
        · exact h1
      rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff)]
      simp
