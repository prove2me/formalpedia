-- Prove2me | solution 1 for Round11.groupoid_balanced_no_leak
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:40:59.514373+00:00
-- url     : https://prove2.me/submissions/02900834-751d-4766-a400-4c6a24e3d476

-- Sol generated from Combinatorics/Round11OrbitCountSeal.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
import Theorems.Thm_Round11_groupoid_orbit_identity
import Theorems.Thm_Round11_ordAt_pos
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
theorem solution{p q b d : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hb : 1 ≤ b) (hcop : Nat.Coprime b (p * q))
    (hdp : ordAt b p = d) (hdq : ordAt b q = d) :
    haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
    Nat.card (Quotient (orbitRel (Subgroup.zpowers (ZMod.unitOfCoprime b hcop))
        (ZMod (p * q)))) * d = d + (p * q - 1) := by
  have hd0 : 0 < d := by
    rw [← hdp]
    refine ordAt_pos hp (fun hdvd => ?_)
    have : p ∣ Nat.gcd b (p * q) := Nat.dvd_gcd hdvd (Dvd.intro q rfl)
    rw [hcop] at this
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hmain := groupoid_orbit_identity hp hq hpq hb hcop
  rw [hdp, hdq, Nat.lcm_self, Nat.div_self hd0, mul_one, mul_one] at hmain
  rw [hmain]
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by have := hp.two_le; omega⟩
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by have := hq.two_le; omega⟩
  have : (p' + 1) * (q' + 1) = p' * q' + p' + q' + 1 := by ring
  simp only [Nat.add_sub_cancel, this]
  omega
