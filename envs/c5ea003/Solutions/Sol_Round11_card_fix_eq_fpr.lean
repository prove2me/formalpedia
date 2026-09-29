-- Prove2me | solution 1 for Round11.card_fix_eq_fpr
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:34:32.534502+00:00
-- url     : https://prove2.me/submissions/4902a64e-f7fa-4d9e-a0fb-61849ad0e40d

-- Sol generated from Combinatorics/Round11OrbitCountSeal.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
import Theorems.Thm_Round11_card_fix_field
import Theorems.Thm_Round11_fpr_eq_indicator
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
theorem solution{p q b k : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hb : 1 ≤ b) :
    haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
    Fintype.card {x : ZMod (p * q) // (b : ZMod (p * q)) ^ k * x = x} = fpr b (p * q) k := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).2 hpq
  set e := ZMod.chineseRemainder hcop with he
  have key : ∀ x : ZMod (p * q), ((b : ZMod (p * q)) ^ k * x = x) ↔
      (((b : ZMod p) ^ k * (e x).1 = (e x).1) ∧ ((b : ZMod q) ^ k * (e x).2 = (e x).2)) := by
    intro x
    exact ⟨fun h => by simpa [Prod.ext_iff] using congrArg e h,
      fun h => e.injective (by simpa [Prod.ext_iff] using h)⟩
  rw [Fintype.card_congr (Equiv.subtypeEquivRight key)]
  rw [Fintype.card_congr (Equiv.subtypeEquiv e.toEquiv (fun _ => Iff.rfl) :
    {x : ZMod (p * q) //
        ((b : ZMod p) ^ k * (e x).1 = (e x).1) ∧ ((b : ZMod q) ^ k * (e x).2 = (e x).2)}
      ≃ {y : ZMod p × ZMod q //
        ((b : ZMod p) ^ k * y.1 = y.1) ∧ ((b : ZMod q) ^ k * y.2 = y.2)})]
  rw [Fintype.card_congr (Equiv.subtypeProdEquivProd
      (p := fun y : ZMod p => (b : ZMod p) ^ k * y = y)
      (q := fun z : ZMod q => (b : ZMod q) ^ k * z = z)),
    Fintype.card_prod, card_fix_field, card_fix_field, ZMod.card, ZMod.card,
    fpr_eq_indicator hp hq hpq hb k]
  rw [if_congr (orderOf_dvd_iff_pow_eq_one (x := (b : ZMod p)) (n := k)).symm rfl rfl,
    if_congr (orderOf_dvd_iff_pow_eq_one (x := (b : ZMod q)) (n := k)).symm rfl rfl]
  rfl
