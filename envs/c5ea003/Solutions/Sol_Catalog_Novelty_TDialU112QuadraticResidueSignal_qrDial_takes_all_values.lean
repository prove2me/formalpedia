-- Prove2me | solution 1 for Catalog.Novelty.TDialU112QuadraticResidueSignal.qrDial_takes_all_values
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:25:13.113436+00:00
-- url     : https://prove2.me/submissions/62da29a7-14bb-43e2-8fd0-94a33cd246ef

-- Sol generated from Novelty/TDialU112QuadraticResidueSignal.lean
import Mathlib
import Definitions.Def_Novelty_TDialU112QuadraticResidueSignal
import Theorems.Thm_Catalog_Novelty_TDialU112QuadraticResidueSignal_two_mul_card_qrSet

/-!
# Where the residual dial signal comes from: exact equidistribution of the small-prime
# quadratic-residue pattern

## Research context (FACT round-70 #1, exp 545, `TDIAL-U112-CONTINUES-FADE`)

The U112 record (see `Novelty.TDialU112FadeReacceleration` for the statistical layer) reports a
pooled Spearman correlation of `0.462` between the dial statistic `T` and a downstream rate,
below the `0.55` band floor, and comments that "the residual `≈ 0.46` correlation is still far
above chance, so the small-prime QR pattern carries real per-`N` signal at bitlen 112".

Every earlier file in the thread treats the dial as an opaque real number attached to a run.
This file supplies the *arithmetic* layer that the sentence above presupposes: it proves, from
scratch, that the small-prime quadratic-residue pattern of a uniformly drawn integer is an
exactly equidistributed family of independent fair bits, so the dial is a genuinely
informative statistic of `N` at every bit length — a fact about `ℤ`, not about the experiment.

The point is a separation of concerns.  What fades with bit length is the *coupling* between
the dial and the downstream rate; the dial's own information content does **not** fade, and
this file computes it exactly.

## Main results

* `two_mul_card_qrSet` — for an odd prime `p`, exactly `(p−1)/2` nonzero residues are squares
  (stated as `2 · |QR(p)| = p − 1`, avoiding truncated division).  Proved from the vanishing
  of the quadratic-character sum.
* `two_mul_card_nqrSet` — the same count for the non-residues.
* `card_filter_crt` — **CRT independence in counting form**: for coprime moduli, the number of
  `x mod mn` whose two reductions satisfy prescribed conditions is the product of the two
  separate counts.  This is the precise sense in which the residue bits at distinct primes are
  independent.
* `card_pattern_SS`, `card_pattern_SN`, `card_pattern_NS`, `card_pattern_NN` — hence each of
  the four QR patterns at two distinct odd primes occurs exactly `(p−1)(q−1)/4` times.
* `qrDial_binomial` — the two-prime dial `T ∈ {0, 1, 2}` therefore has the exact
  `Binomial(2, 1/2)` law: `4·|T = 0| = 2·|T = 1| = 4·|T = 2| = (p−1)(q−1)`.
* `qrDial_takes_all_values` — all three levels are attained, so the dial is a nonconstant
  statistic on the unit part.
* `two_mul_dial_variance` — the exact second moment: `2 ∑ (T − 1)² = |units|`, i.e. the dial
  has variance exactly `1/2` — independent of the primes and hence of the bit length.

## Lab notes (exp 545, arithmetic layer)

```
p = 3,  q = 5 : |QR(3)| = 1, |QR(5)| = 2, pattern counts 2,2,2,2, dial law 2:4:2
p = 7,  q = 11: |QR(7)| = 3, |QR(11)| = 5, pattern counts 15 each, dial law 15:30:15
dial mean     : 1                       dial variance : 1/2   (all primes, all bitlens)
```
-/

open Finset
open scoped Classical

open Catalog.Novelty.TDialU112QuadraticResidueSignal

/-! ## 1. The residue count at a single small prime -/



lemma card_qrSet_add_card_nqrSet (p : ℕ) [Fact p.Prime] :
    (qrSet p).card + (nqrSet p).card = p - 1 := by
  have hS : Finset.filter (fun a : ZMod p => IsSquare a)
        (univ.filter (fun a : ZMod p => a ≠ 0)) = qrSet p := Finset.filter_filter _ _ _
  have hN : Finset.filter (fun a : ZMod p => ¬ IsSquare a)
        (univ.filter (fun a : ZMod p => a ≠ 0)) = nqrSet p := Finset.filter_filter _ _ _
  rw [← hS, ← hN, Finset.card_filter_add_card_filter_not]
  have hE : (univ.filter (fun a : ZMod p => a ≠ 0)) = univ.erase (0 : ZMod p) := by
    ext a; simp [Finset.mem_erase]
  rw [hE, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, ZMod.card]


/-- The matching count for the non-residues. -/
theorem two_mul_card_nqrSet (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) :
    2 * (nqrSet p).card = p - 1 := by
  have h1 := two_mul_card_qrSet p hp
  have h2 := card_qrSet_add_card_nqrSet p
  omega



/-! ## 2. CRT independence of the residue bits -/



lemma chineseRemainder_fst {m n : ℕ} (h : m.Coprime n) (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h x).1 = redFst m n x := by
  have hcomp : (RingHom.fst (ZMod m) (ZMod n)).comp
      (ZMod.chineseRemainder h : ZMod (m * n) →+* _) = redFst m n := RingHom.ext_zmod _ _
  exact congrArg (fun f => f x) hcomp

lemma chineseRemainder_snd {m n : ℕ} (h : m.Coprime n) (x : ZMod (m * n)) :
    (ZMod.chineseRemainder h x).2 = redSnd m n x := by
  have hcomp : (RingHom.snd (ZMod m) (ZMod n)).comp
      (ZMod.chineseRemainder h : ZMod (m * n) →+* _) = redSnd m n := RingHom.ext_zmod _ _
  exact congrArg (fun f => f x) hcomp

/-- **CRT independence, counting form.**  For coprime moduli the two reduction bits are
statistically independent: the number of residues mod `mn` satisfying a condition at `m` *and*
a condition at `n` is the product of the two individual counts. -/
theorem card_filter_crt {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (h : m.Coprime n) (P : ZMod m → Prop) (Q : ZMod n → Prop) :
    (univ.filter (fun x : ZMod (m * n) => P (redFst m n x) ∧ Q (redSnd m n x))).card
      = (univ.filter P).card * (univ.filter Q).card := by
  rw [← Finset.card_product]
  refine Finset.card_equiv (ZMod.chineseRemainder h).toEquiv ?_
  intro x
  simp only [mem_filter, mem_univ, true_and, Finset.mem_product, RingEquiv.toEquiv_eq_coe,
    RingEquiv.coe_toEquiv]
  rw [chineseRemainder_fst h x, chineseRemainder_snd h x]

/-! ## 3. The two-prime dial and its exact law -/

variable (p q : ℕ) [Fact p.Prime] [Fact q.Prime]






variable {p q}

/-- **Each QR pattern occurs exactly `(p−1)(q−1)/4` times.**  (Stated as
`4 · count = (p−1)(q−1)`.) -/
theorem card_pattern_SS (hpq : p ≠ q) (hp : p ≠ 2) (hq : q ≠ 2) :
    4 * (patternSS p q).card = (p - 1) * (q - 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes Fact.out Fact.out).mpr hpq
  have h := card_filter_crt (m := p) (n := q) hcop (· ∈ qrSet p) (· ∈ qrSet q)
  have hP := two_mul_card_qrSet p hp
  have hQ := two_mul_card_qrSet q hq
  have hcard : (patternSS p q).card = (qrSet p).card * (qrSet q).card := by
    rw [patternSS]; convert h using 3 <;> simp [qrSet]
  rw [hcard]
  calc 4 * ((qrSet p).card * (qrSet q).card)
      = (2 * (qrSet p).card) * (2 * (qrSet q).card) := by ring
    _ = (p - 1) * (q - 1) := by rw [hP, hQ]

theorem card_pattern_SN (hpq : p ≠ q) (hp : p ≠ 2) (hq : q ≠ 2) :
    4 * (patternSN p q).card = (p - 1) * (q - 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes Fact.out Fact.out).mpr hpq
  have h := card_filter_crt (m := p) (n := q) hcop (· ∈ qrSet p) (· ∈ nqrSet q)
  have hP := two_mul_card_qrSet p hp
  have hQ := two_mul_card_nqrSet q hq
  have hcard : (patternSN p q).card = (qrSet p).card * (nqrSet q).card := by
    rw [patternSN]; convert h using 3 <;> simp [qrSet, nqrSet]
  rw [hcard]
  calc 4 * ((qrSet p).card * (nqrSet q).card)
      = (2 * (qrSet p).card) * (2 * (nqrSet q).card) := by ring
    _ = (p - 1) * (q - 1) := by rw [hP, hQ]


theorem card_pattern_NN (hpq : p ≠ q) (hp : p ≠ 2) (hq : q ≠ 2) :
    4 * (patternNN p q).card = (p - 1) * (q - 1) := by
  have hcop : Nat.Coprime p q := (Nat.coprime_primes Fact.out Fact.out).mpr hpq
  have h := card_filter_crt (m := p) (n := q) hcop (· ∈ nqrSet p) (· ∈ nqrSet q)
  have hP := two_mul_card_nqrSet p hp
  have hQ := two_mul_card_nqrSet q hq
  have hcard : (patternNN p q).card = (nqrSet p).card * (nqrSet q).card := by
    rw [patternNN]; convert h using 3 <;> simp [nqrSet]
  rw [hcard]
  calc 4 * ((nqrSet p).card * (nqrSet q).card)
      = (2 * (nqrSet p).card) * (2 * (nqrSet q).card) := by ring
    _ = (p - 1) * (q - 1) := by rw [hP, hQ]

/-! ### The dial level sets -/

lemma qrSet_nqrSet_disjoint (m : ℕ) [NeZero m] {a : ZMod m} (h1 : a ∈ qrSet m) :
    a ∉ nqrSet m := by
  simp only [qrSet, nqrSet, mem_filter, mem_univ, true_and] at h1 ⊢
  exact fun h2 => h2.2 h1.2

lemma qrDial_eq_two {x : ZMod (p * q)} (hx : x ∈ patternSS p q) : qrDial p q x = 2 := by
  simp only [patternSS, mem_filter, mem_univ, true_and] at hx
  simp [qrDial, hx.1, hx.2]

lemma qrDial_eq_zero {x : ZMod (p * q)} (hx : x ∈ patternNN p q) : qrDial p q x = 0 := by
  simp only [patternNN, mem_filter, mem_univ, true_and] at hx
  have h1 : redFst p q x ∉ qrSet p := fun h => qrSet_nqrSet_disjoint p h hx.1
  have h2 : redSnd p q x ∉ qrSet q := fun h => qrSet_nqrSet_disjoint q h hx.2
  simp [qrDial, h1, h2]

lemma qrDial_eq_one_SN {x : ZMod (p * q)} (hx : x ∈ patternSN p q) : qrDial p q x = 1 := by
  simp only [patternSN, mem_filter, mem_univ, true_and] at hx
  have h2 : redSnd p q x ∉ qrSet q := fun h => qrSet_nqrSet_disjoint q h hx.2
  simp [qrDial, hx.1, h2]











open Catalog.Novelty.TDialU112QuadraticResidueSignal in
theorem solution(hpq : p ≠ q) (hp : p ≠ 2) (hq : q ≠ 2) :
    (∃ x : ZMod (p * q), qrDial p q x = 0) ∧ (∃ x : ZMod (p * q), qrDial p q x = 1) ∧
      (∃ x : ZMod (p * q), qrDial p q x = 2) := by
  have hp3 : 3 ≤ p := by have := (Fact.out : p.Prime).two_le; omega
  have hq3 : 3 ≤ q := by have := (Fact.out : q.Prime).two_le; omega
  have hprod : 0 < (p - 1) * (q - 1) := Nat.mul_pos (by omega) (by omega)
  have hSS : 0 < (patternSS p q).card := by
    have := card_pattern_SS hpq hp hq; omega
  have hNN : 0 < (patternNN p q).card := by
    have := card_pattern_NN hpq hp hq; omega
  have hSN : 0 < (patternSN p q).card := by
    have := card_pattern_SN hpq hp hq; omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hSS
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hNN
  obtain ⟨z, hz⟩ := Finset.card_pos.mp hSN
  exact ⟨⟨y, qrDial_eq_zero hy⟩, ⟨z, qrDial_eq_one_SN hz⟩, ⟨x, qrDial_eq_two hx⟩⟩
