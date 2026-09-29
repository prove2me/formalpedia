-- Prove2me | solution 1 for Round11.groupoid_orbit_identity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T00:39:33.987499+00:00
-- url     : https://prove2.me/submissions/d17dfdf7-e3fa-43c3-90dc-4ac874d753c1

-- Sol generated from Combinatorics/Round11OrbitCountSeal.lean
import Mathlib
import Definitions.Def_Combinatorics_Round11CycleIndexFingerprint
import Theorems.Thm_Round11_card_fix_eq_fpr
import Theorems.Thm_Round11_fpr_eq_indicator
import Theorems.Thm_Round11_ordAt_pos
import Theorems.Thm_Round11_orderOf_semiprime
import Theorems.Thm_Round11_period_sum_indicator
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
theorem solution{p q b : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hb : 1 ≤ b) (hcop : Nat.Coprime b (p * q)) :
    haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
    Nat.card (Quotient (orbitRel (Subgroup.zpowers (ZMod.unitOfCoprime b hcop)) (ZMod (p * q))))
        * Nat.lcm (ordAt b p) (ordAt b q)
      = Nat.lcm (ordAt b p) (ordAt b q)
        + (p - 1) * (Nat.lcm (ordAt b p) (ordAt b q) / ordAt b p)
        + (q - 1) * (Nat.lcm (ordAt b p) (ordAt b q) / ordAt b q)
        + (p - 1) * (q - 1) := by
  classical
  haveI : NeZero (p * q) := ⟨Nat.mul_ne_zero hp.ne_zero hq.ne_zero⟩
  have hbp : ¬ p ∣ b := by
    intro h
    have : p ∣ Nat.gcd b (p * q) := Nat.dvd_gcd h (Dvd.intro q rfl)
    rw [hcop] at this
    exact Nat.Prime.one_lt hp |>.ne' (Nat.dvd_one.1 this)
  have hbq : ¬ q ∣ b := by
    intro h
    have : q ∣ Nat.gcd b (p * q) := Nat.dvd_gcd h (Dvd.intro_left p rfl)
    rw [hcop] at this
    exact Nat.Prime.one_lt hq |>.ne' (Nat.dvd_one.1 this)
  set u := ZMod.unitOfCoprime b hcop with hu
  have hfin : IsOfFinOrder u := isOfFinOrder_of_finite u
  have hcoe : ((u : (ZMod (p * q))ˣ) : ZMod (p * q)) = (b : ZMod (p * q)) :=
    ZMod.coe_unitOfCoprime b hcop
  have horder : orderOf u = Nat.lcm (ordAt b p) (ordAt b q) := by
    rw [← orderOf_units, hcoe, orderOf_semiprime hp hq hpq]
  haveI : Fintype (Quotient (orbitRel (↥(Subgroup.zpowers u)) (ZMod (p * q)))) :=
    Fintype.ofFinite _
  -- Burnside's lemma
  have hburn := MulAction.sum_card_fixedBy_eq_card_orbits_mul_card_group
    (↥(Subgroup.zpowers u)) (ZMod (p * q))
  -- the sum of fixed-point counts is the period sum of the fingerprint
  have hsum : ∑ a : ↥(Subgroup.zpowers u), Fintype.card (fixedBy (ZMod (p * q)) a)
      = ∑ k ∈ range (orderOf u), fpr b (p * q) k := by
    rw [← Equiv.sum_comp (finEquivZPowers hfin)
      (fun a => Fintype.card (fixedBy (ZMod (p * q)) a)),
      ← Fin.sum_univ_eq_sum_range (fun k => fpr b (p * q) k) (orderOf u)]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [finEquivZPowers_apply hfin]
    rw [← card_fix_eq_fpr (k := (i : ℕ)) hp hq hpq hb]
    refine Fintype.card_congr (Equiv.subtypeEquivRight (fun x => ?_))
    show ((⟨u ^ (i : ℕ), _⟩ : Subgroup.zpowers u) • x = x) ↔ _
    simp [Units.smul_def, hu, ZMod.coe_unitOfCoprime]
  -- evaluate the period sum
  have hperiod : ∑ k ∈ range (orderOf u), fpr b (p * q) k
      = Nat.lcm (ordAt b p) (ordAt b q)
        + (p - 1) * (Nat.lcm (ordAt b p) (ordAt b q) / ordAt b p)
        + (q - 1) * (Nat.lcm (ordAt b p) (ordAt b q) / ordAt b q)
        + (p - 1) * (q - 1) := by
    have hcongr : ∀ k ∈ range (Nat.lcm (ordAt b p) (ordAt b q)), fpr b (p * q) k
        = (if ordAt b p ∣ k then p else 1) * (if ordAt b q ∣ k then q else 1) :=
      fun k _ => fpr_eq_indicator hp hq hpq hb k
    rw [horder, Finset.sum_congr rfl hcongr]
    exact period_sum_indicator p q (ordAt b p) (ordAt b q) hp.pos hq.pos
      (ordAt_pos hp hbp) (ordAt_pos hq hbq)
  rw [hsum, hperiod, Fintype.card_zpowers, horder] at hburn
  rw [Nat.card_eq_fintype_card]
  exact hburn.symm
