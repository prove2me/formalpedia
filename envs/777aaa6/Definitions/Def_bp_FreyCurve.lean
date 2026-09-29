-- Prove2me | Definitions.Def_bp_FreyCurve
-- name    : bp_FreyCurve
-- status  : Definition
-- author  : @tianyipeng
-- created : 2026-05-20T21:07:06.698793+00:00
-- url     : https://prove2.me/theorems/e8b2d9ad-9dff-49b5-9324-7128b1def093
-- statement:
--   **The Frey curve and its arithmetic.** For a Frey package (a,b,c,p), the Frey curve is the elliptic curve Y² + XY = X³ + ((bᵖ−1−aᵖ)/4)X² − (aᵖbᵖ/16)X over ℚ (the integral model of Y² = X(X−aᵖ)(X+bᵖ), normalized to be semistable at 2). This module proves: the discriminant Δ = (abc)^{2p}/2⁸ ≠ 0 (so the curve is elliptic), the invariants b₂, b₄, c₄, the j-invariant j = 2⁸·(c^{2p}−(ab)ᵖ)³/(abc)^{2p}, and the key Serre observation that ord_q(j) ≡ 0 mod p for every odd prime q of bad reduction — the input to the semistability and ramification analysis of the mod-p Galois representation. Ported from the Imperial College FLT formalization (FLT/Basic/FreyPackage.lean), verified against Mathlib. Import via `import Definitions.Def_bp_FreyCurve` (also requires `Definitions.Def_bp_FreyPackage`).
-- source:
--   Imperial College FLT blueprint §2.5–2.6 / Serre 1987 §4.1

/-
Frey curve definition + elementary lemmas, ported from the Imperial College FLT
formalization (`FLT/Basic/FreyPackage.lean`,
https://github.com/ImperialCollegeLondon/FLT, blueprint §2.5–2.6, Apache 2.0).

Authors of the original: Kevin Buzzard, Ruben Van de Velde, Pietro Monticone.
Ported to vanilla Mathlib v4.29.0 for the prove2me FLT decomposition.
-/
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic.ModCases
import Mathlib.Tactic.Rify
import Mathlib.Tactic.Positivity
import Definitions.Def_bp_FreyPackage

set_option autoImplicit false


namespace FreyPackage

lemma hppos (P : FreyPackage) : 0 < P.p := lt_of_lt_of_le (by omega) P.hp5

lemma hp0 (P : FreyPackage) : P.p ≠ 0 := P.hppos.ne'

lemma hp_odd (P : FreyPackage) : Odd P.p := Nat.Prime.odd_of_ne_two P.pp <|
  have := P.hp5; by linarith

/-- Any common factor of two of `a`, `b`, `c` with `a^p + b^p = c^p` divides the
third, so `gcd a b = gcd a c`. -/
lemma gcdab_eq_gcdac {a b c : ℤ} {p : ℕ} (hp : 0 < p) (h : a ^ p + b ^ p = c ^ p) :
    gcd a b = gcd a c := by
  have foo : gcd a b ∣ gcd a c := by
    apply dvd_gcd (gcd_dvd_left a b)
    rw [← Int.pow_dvd_pow_iff hp.ne', ← h]
    apply dvd_add <;> rw [Int.pow_dvd_pow_iff hp.ne']
    · exact gcd_dvd_left a b
    · exact gcd_dvd_right a b
  have bar : gcd a c ∣ gcd a b := by
    apply dvd_gcd (gcd_dvd_left a c)
    have h2 : b ^ p = c ^ p - a ^ p := eq_sub_of_add_eq' h
    rw [← Int.pow_dvd_pow_iff hp.ne', h2]
    apply dvd_add
    · rw [Int.pow_dvd_pow_iff hp.ne']
      exact gcd_dvd_right a c
    · rw [dvd_neg, Int.pow_dvd_pow_iff hp.ne']
      exact gcd_dvd_left a c
  change _ ∣ (Int.gcd a c : ℤ) at foo
  apply Int.ofNat_dvd.1 at bar
  apply Int.ofNat_dvd.1 at foo
  exact congr_arg ((↑) : ℕ → ℤ) <| Nat.dvd_antisymm foo bar

lemma hgcdac (P : FreyPackage) : gcd P.a P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos P.hFLT, P.hgcdab]

lemma hgcdbc (P : FreyPackage) : gcd P.b P.c = 1 := by
  rw [← gcdab_eq_gcdac P.hppos, gcd_comm, P.hgcdab]
  rw [add_comm]
  exact P.hFLT

/-- The Weierstrass curve over `ℤ` associated to a Frey package. The conditions imposed
upon a Frey package guarantee that the running hypotheses in
Section 4.1 of [Serre] all hold. We put the curve into the form where the
equation is semistable at 2, rather than the usual `Y^2 = X(X - a^p)(X + b^p)` form.
The change of variables is `X = 4x`, `Y = 8y + 4x`, then divide through by 64. -/
def freyCurveInt (P : FreyPackage) : WeierstrassCurve ℤ where
  a₁ := 1
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4   -- numerator is a multiple of 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16   -- numerator is a multiple of 16
  a₆ := 0

/-- The elliptic curve over `ℚ` associated to a Frey package — same coefficients as
`freyCurveInt`, but read in `ℚ` so the divisions are exact. -/
def freyCurve (P : FreyPackage) : WeierstrassCurve ℚ where
  a₁ := 1
  a₂ := (P.b ^ P.p - 1 - P.a ^ P.p) / 4
  a₃ := 0
  a₄ := -(P.a ^ P.p) * (P.b ^ P.p) / 16
  a₆ := 0

end FreyPackage

namespace FreyCurve

open FreyPackage

/-- The integral model `freyCurveInt` maps to the rational `freyCurve` under `ℤ → ℚ`. -/
theorem map (P : FreyPackage) : (freyCurveInt P).map (algebraMap ℤ ℚ) = freyCurve P := by
  have two_dvd_b : 2 ∣ P.b := (ZMod.intCast_zmod_eq_zero_iff_dvd P.b 2).1 P.hb2
  ext
  · rfl
  · change (((P.b ^ P.p - 1 - P.a ^ P.p) / 4 : ℤ) : ℚ) = (P.b ^ P.p - 1 - P.a ^ P.p) / 4
    rw [Rat.intCast_div]
    · norm_cast
    · rw [sub_sub]
      apply Int.dvd_sub
      · calc
          (4 : ℤ) = 2 ^ 2     := by norm_num
          _       ∣ P.b ^ 2   := pow_dvd_pow_of_dvd two_dvd_b 2
          _       ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
      · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).1
        push_cast
        rw [P.ha4, show (3 : ZMod 4) = -1 from rfl, neg_one_pow_eq_ite, if_neg]
        · norm_num
        · rw [Nat.Prime.even_iff P.pp]
          linarith [P.hp5]
  · rfl
  · change ((-(P.a ^ P.p) * (P.b ^ P.p) / 16 : ℤ) : ℚ) = -(P.a ^ P.p) * (P.b ^ P.p) / 16
    rw [Rat.intCast_div]
    · norm_cast
    · calc
        (16 : ℤ) = 2 ^ 4     := by norm_num
        _        ∣ P.b ^ 4   := pow_dvd_pow_of_dvd two_dvd_b 4
        _        ∣ P.b ^ P.p := pow_dvd_pow P.b (by linarith [P.hp5])
        _        ∣ _         := Int.dvd_mul_left _ _
  · rfl

#print axioms FreyCurve.map

/-- The discriminant of the Frey curve is `(abc)^{2p} / 2^8`. -/
lemma Δ (P : FreyPackage) : P.freyCurve.Δ = (P.a * P.b * P.c) ^ (2 * P.p) / 2 ^ 8 := by
  trans (P.a ^ P.p) ^ 2 * (P.b ^ P.p) ^ 2 * (P.c ^ P.p) ^ 2 / 2 ^ 8
  · field_simp
    norm_cast
    simp [← P.hFLT, WeierstrassCurve.Δ, freyCurve, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
      WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    ring
  · simp [← mul_pow, ← pow_mul, mul_comm 2]

#print axioms FreyCurve.Δ

/-- The Frey curve is an elliptic curve: its discriminant is nonzero. -/
instance (P : FreyPackage) : WeierstrassCurve.IsElliptic (freyCurve P) where
  isUnit := by
    rw [FreyCurve.Δ, isUnit_iff_ne_zero]
    apply div_ne_zero
    · norm_cast
      exact pow_ne_zero _ <| mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0
    · norm_num

/-- Quick check: the IsElliptic instance synthesizes. -/
example (P : FreyPackage) : (freyCurve P).IsElliptic := inferInstance

lemma b₂ (P : FreyPackage) :
    P.freyCurve.b₂ = P.b ^ P.p - P.a ^ P.p := by
  simp [freyCurve, WeierstrassCurve.b₂]
  ring

#print axioms FreyCurve.b₂

lemma b₄ (P : FreyPackage) :
    P.freyCurve.b₄ = -(P.a * P.b) ^ P.p / 8 := by
  simp [freyCurve, WeierstrassCurve.b₄]
  ring

#print axioms FreyCurve.b₄

lemma c₄ (P : FreyPackage) :
    P.freyCurve.c₄ = (P.a ^ P.p) ^ 2 + P.a ^ P.p * P.b ^ P.p + (P.b ^ P.p) ^ 2 := by
  simp [FreyCurve.b₂, FreyCurve.b₄, WeierstrassCurve.c₄]
  ring

#print axioms FreyCurve.c₄

lemma c₄' (P : FreyPackage) :
    P.freyCurve.c₄ = P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p := by
  rw [FreyCurve.c₄]
  rw_mod_cast [pow_mul', ← hFLT]
  ring

#print axioms FreyCurve.c₄'

lemma Δ'inv (P : FreyPackage) :
    (↑(P.freyCurve.Δ'⁻¹) : ℚ) = 2 ^ 8 / (P.a * P.b * P.c) ^ (2 * P.p) := by
  simp [FreyCurve.Δ]

#print axioms FreyCurve.Δ'inv

/-- The j-invariant of the Frey curve. -/
lemma j (P : FreyPackage) :
    P.freyCurve.j = 2 ^ 8 * (P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p) ^ 3 / (P.a * P.b * P.c) ^ (2 * P.p) := by
  rw [mul_div_right_comm, WeierstrassCurve.j, FreyCurve.Δ'inv, FreyCurve.c₄']

#print axioms FreyCurve.j

private lemma j_pos_aux (a b : ℤ) (hb : b ≠ 0) : 0 < (a + b) ^ 2 - a * b := by
  rify
  calc
    (0 : ℝ) < ((a : ℝ) ^ 2 + ((a : ℝ) + (b : ℝ)) ^ 2 + (b : ℝ) ^ 2) / 2 := by positivity
    _ = ((a : ℝ) + (b : ℝ)) ^ 2 - (a : ℝ) * (b : ℝ) := by ring

/-- The q-adic valuation of the j-invariant of the Frey curve is a multiple of `p`
when `q > 2` is a prime of bad reduction. This is the key Serre observation tying
the Frey curve to semistability and the eventual modularity argument. -/
lemma j_valuation_of_bad_prime (P : FreyPackage) {q : ℕ} (hqPrime : q.Prime)
    (hqbad : (q : ℤ) ∣ P.a * P.b * P.c) (hqodd : 2 < q) :
    (P.p : ℤ) ∣ padicValRat q P.freyCurve.j := by
  have := Fact.mk hqPrime
  have hqPrime' := Nat.prime_iff_prime_int.mp hqPrime
  have h₀ : ((P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p) ^ 3 : ℚ) ≠ 0 := by
    rw_mod_cast [pow_mul', ← P.hFLT, mul_pow]
    exact pow_ne_zero _ <| ne_of_gt <| j_pos_aux _ _ (pow_ne_zero _ P.hb0)
  have h₁ : P.a * P.b * P.c ≠ 0 := mul_ne_zero (mul_ne_zero P.ha0 P.hb0) P.hc0
  rw [FreyCurve.j, padicValRat.div (mul_ne_zero (by norm_num) h₀) (pow_ne_zero _ (mod_cast h₁)),
    padicValRat.mul (by norm_num) h₀, padicValRat.pow two_ne_zero, ← Nat.cast_two,
    ← padicValRat_of_nat, padicValNat_primes hqodd.ne', Nat.cast_zero, mul_zero, zero_add]
  have : ¬ (q : ℤ) ∣ (P.c ^ (2 * P.p) - (P.a * P.b) ^ P.p) ^ 3 := by
    rw [hqPrime'.dvd_pow_iff_dvd three_ne_zero]
    have hq' : Xor' ((q : ℤ) ∣ P.a * P.b) ((q : ℤ) ∣ P.c) := by
      rw [xor_iff_not_iff, iff_iff_and_or_not_and_not]
      rintro (⟨hab, hc⟩ | ⟨hab, hc⟩)
      · rw [hqPrime'.dvd_mul] at hab
        apply hqPrime'.not_dvd_one
        cases hab with
        | inl ha => rw [← P.hgcdac]; exact dvd_gcd ha hc
        | inr hb => rw [← P.hgcdbc]; exact dvd_gcd hb hc
      · rw [hqPrime'.dvd_mul] at hqbad
        exact hqbad.rec hab hc
    have h2p0 := mul_ne_zero two_ne_zero P.hp0
    cases hq' with
    | inl h =>
      rw [dvd_sub_left (dvd_pow h.1 P.hp0), hqPrime'.dvd_pow_iff_dvd h2p0]
      exact h.2
    | inr h =>
      rw [dvd_sub_right (dvd_pow h.1 h2p0), hqPrime'.dvd_pow_iff_dvd P.hp0]
      exact h.2
  norm_cast
  rw [padicValRat.of_int, padicValInt.eq_zero_of_not_dvd this, Nat.cast_zero, zero_sub,
    Int.cast_pow, padicValRat.pow (mod_cast h₁), dvd_neg, Nat.cast_mul]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

#print axioms FreyCurve.j_valuation_of_bad_prime

end FreyCurve


