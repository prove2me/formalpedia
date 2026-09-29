-- Prove2me | solution 2 for PlusOneWilliams.dvd_lucasV_sub_two
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T17:57:23.259058+00:00
-- url     : https://prove2.me/submissions/2f93abc0-5abb-4dc4-bc01-95491c80e124

import Mathlib
import Definitions.Def_Tropical_PlusOneWilliamsCore

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Tropical/PlusOneWilliamsCore.lean ====
/-!
# The Williams `p + 1` method: Lucas sequences and the discriminant gate

This file formalises the *arithmetic core* of the round-16 experiment
`PLUSONE-SMOOTH-NULL` (paper 64). The experiment measured, over 40 matched
semiprime pairs, that the classical Williams `p + 1` method (bases `P = 3, 5, 7`,
exponent `M = lcm(1..100)`) factors the `PLUSONE` class 24/40 and the `GENERAL`
class 0/40, and — the new structural finding — that the per-base success set is
*exactly* the set of instances with `(D | p) = -1`, where `D = P² - 4` is the
discriminant of the Lucas sequence.

Here we prove the theorems behind those numbers.

* `lucasV` — the Lucas `V`-sequence with parameters `(P, Q = 1)`, over any
  commutative ring; `lucasV_eq_pow_add_pow` is its Binet form.
* `lucasV_eq_two_of_nonsquare_disc` — **the `p + 1` half of the gate.** If
  `D = P² - 4` is a non-square mod the odd prime `p` and `(p + 1) ∣ M`, then
  `V_M ≡ 2 (mod p)`. The proof builds the quadratic extension
  `𝔽_p[X]/(X² - D) ≅ 𝔽_{p²}`, exhibits the two conjugate roots
  `a, b = (P ± √D)/2` of `x² - Px + 1`, and shows the Frobenius swaps them, so
  `a^{p+1} = ab = 1`.
* `lucasV_eq_two_of_square_disc` — **the `p - 1` half of the gate.** If `D` is a
  square mod `p` the roots are already in `𝔽_p`, so the relevant order divides
  `p - 1`, not `p + 1`: the method silently degenerates to Pollard `p - 1`.
  This is why the observed success rate equals the `(D | p) = -1` rate exactly.
* `williams_gcd_eq_factor` — the gcd step really returns the factor `p`.
* `lucasV_two_eq_two`, `plusOne_base_two_degenerate` — the base `P = 2` has
  `D = 0` and the sequence is constant `2`, so the gcd is always `N`: the
  degenerate base observed in the experiment.
* `legendreSym_fortyfive_eq_five`, `base_three_seven_same_gate` — `D₃ = 5` and
  `D₇ = 45 = 5 · 3²` lie in the same square class, so bases `3` and `7` succeed
  on *exactly* the same primes (observed: 11/40 for both, on the same instances).
-/

namespace PlusOneWilliams

open Polynomial

/-! ## 1. The Lucas `V`-sequence with `Q = 1` -/

-- [dropped: platform already declares lucasV]
@[simp] lemma lucasV_zero {R : Type*} [CommRing R] (P : R) : lucasV P 0 = 2 := rfl

@[simp] lemma lucasV_one {R : Type*} [CommRing R] (P : R) : lucasV P 1 = P := rfl

lemma lucasV_succ_succ {R : Type*} [CommRing R] (P : R) (n : ℕ) :
    lucasV P (n + 2) = P * lucasV P (n + 1) - lucasV P n := rfl

/-- The Lucas sequence commutes with ring homomorphisms (reduction mod `p`). -/
lemma map_lucasV {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (P : R) (n : ℕ) :
    f (lucasV P n) = lucasV (f P) n := by
  induction n using Nat.twoStepInduction with
  | zero => exact map_ofNat f 2
  | one => rfl
  | more n ih1 ih2 => simp [lucasV_succ_succ, ih1, ih2]

/-- **Binet form.** If `a·b = 1` and `a + b = P` then `V_n = aⁿ + bⁿ`. -/
lemma lucasV_eq_pow_add_pow {R : Type*} [CommRing R] {P a b : R}
    (hab : a * b = 1) (hsum : a + b = P) (n : ℕ) :
    lucasV P n = a ^ n + b ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => show (2 : R) = _; norm_num
  | one => show P = _; simp [← hsum]
  | more n ih1 ih2 =>
      rw [lucasV_succ_succ, ih1, ih2, ← hsum]
      have h : a ^ (n + 2) + b ^ (n + 2)
          = (a + b) * (a ^ (n + 1) + b ^ (n + 1)) - (a * b) * (a ^ n + b ^ n) := by ring
      rw [h, hab]; ring

/-- If both conjugate roots are killed by the exponent `M`, then `V_M = 2`. -/
lemma lucasV_eq_two_of_pow_eq_one {R : Type*} [CommRing R] {P a b : R}
    (hab : a * b = 1) (hsum : a + b = P) {M : ℕ} (ha : a ^ M = 1) (hb : b ^ M = 1) :
    lucasV P M = 2 := by
  rw [lucasV_eq_pow_add_pow hab hsum, ha, hb]; norm_num

/-- **The exact success criterion.** Over a domain, `V_M = 2` holds *if and
only if* the root `a` satisfies `a^M = 1`; i.e. the Williams method succeeds at
`p` for exponent `M` exactly when the order of `a` in the norm-one torus
divides `M`. Divisibility `(p+1) ∣ M` is the sufficient condition the classical
algorithm can arrange. -/
theorem lucasV_eq_two_iff_pow_eq_one {K : Type*} [CommRing K] [IsDomain K] {P a b : K}
    (hab : a * b = 1) (hsum : a + b = P) (M : ℕ) :
    lucasV P M = 2 ↔ a ^ M = 1 := by
  have habM : a ^ M * b ^ M = 1 := by rw [← mul_pow, hab, one_pow]
  have key : a ^ M * (lucasV P M - 2) = (a ^ M - 1) ^ 2 := by
    rw [lucasV_eq_pow_add_pow hab hsum]
    have h : a ^ M * (a ^ M + b ^ M - 2) = a ^ M * a ^ M + (a ^ M * b ^ M) - 2 * a ^ M := by ring
    rw [h, habM]; ring
  constructor
  · intro h
    rw [h, sub_self, mul_zero] at key
    have h0 := (pow_eq_zero_iff (n := 2) (by norm_num)).mp key.symm
    linear_combination h0
  · intro h
    have h1 : b ^ M = 1 := by rw [h, one_mul] at habM; exact habM
    rw [lucasV_eq_pow_add_pow hab hsum, h, h1]; norm_num

/-! ## 2. The `p + 1` half of the discriminant gate -/

/-- Abstract core of the Williams theorem: in any commutative ring `K` of
characteristic `p` receiving `ZMod p` injectively and containing a square root
`s` of the discriminant `D = P² - 4` with `s^p = -s` (i.e. `D` is a non-residue),
the Lucas sequence satisfies `V_M = 2` whenever `(p + 1) ∣ M`. -/
theorem lucasV_eq_two_aux {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {K : Type*} [CommRing K]
    [CharP K p] (f : ZMod p →+* K) (hinj : Function.Injective f) (P : ZMod p) (s : K)
    (hs2 : s ^ 2 = f (P ^ 2 - 4)) (hsp : s ^ p = -s) {M : ℕ} (hM : (p + 1) ∣ M) :
    lucasV P M = 2 := by
  have hp' : p.Prime := Fact.out
  have hodd : Odd p := hp'.odd_of_ne_two hp2
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp h)
    simpa using h2
  set c : K := f ((2 : ZMod p)⁻¹) with hc
  have hc2 : f 2 * c = 1 := by rw [hc, ← map_mul, mul_inv_cancel₀ h2ne, map_one]
  set a : K := (f P + s) * c with ha
  set b : K := (f P + -s) * c with hb
  have hsum : a + b = f P := by
    have h : a + b = f 2 * c * f P := by rw [ha, hb, map_ofNat]; ring
    rw [h, hc2, one_mul]
  have hab : a * b = 1 := by
    have h4 : f 4 = f 2 * f 2 := by rw [← map_mul]; norm_num
    have hfd : f (P ^ 2 - 4) = f P * f P - f 4 := by rw [map_sub, map_pow]; ring
    have h1 : a * b = (f P * f P - s ^ 2) * (c * c) := by rw [ha, hb]; ring
    rw [h1, hs2, hfd, h4]
    calc (f P * f P - (f P * f P - f 2 * f 2)) * (c * c) = (f 2 * c) * (f 2 * c) := by ring
      _ = 1 := by rw [hc2]; ring
  have hfP : (f P) ^ p = f P := by rw [← map_pow, ZMod.pow_card]
  have hcp : c ^ p = c := by rw [hc, ← map_pow, ZMod.pow_card]
  have hap : a ^ p = b := by
    rw [ha, mul_pow, add_pow_char _ _ p, hfP, hsp, hcp, hb]
  have hbp : b ^ p = a := by
    rw [hb, mul_pow, add_pow_char _ _ p, hfP, hodd.neg_pow, hsp, hcp, ha, neg_neg]
  have hapow : a ^ (p + 1) = 1 := by rw [pow_succ, hap, ← hab]; ring
  have hbpow : b ^ (p + 1) = 1 := by rw [pow_succ, hbp, ← hab]
  obtain ⟨k, rfl⟩ := hM
  have hA : a ^ ((p + 1) * k) = 1 := by rw [pow_mul, hapow, one_pow]
  have hB : b ^ ((p + 1) * k) = 1 := by rw [pow_mul, hbpow, one_pow]
  have key : f (lucasV P ((p + 1) * k)) = f 2 := by
    rw [map_lucasV, lucasV_eq_two_of_pow_eq_one hab hsum hA hB, map_ofNat]
  exact hinj key

/-- **The `p + 1` half of the discriminant gate.** For an odd prime `p` and a
base `P` whose discriminant `D = P² - 4` is a non-square mod `p`, the Lucas
sequence satisfies `V_M ≡ 2 (mod p)` for every exponent `M` divisible by
`p + 1`. This is the correctness statement of the Williams (1982) method. -/
theorem lucasV_eq_two_of_nonsquare_disc (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P : ZMod p)
    (hD : ¬ IsSquare (P ^ 2 - 4)) {M : ℕ} (hM : (p + 1) ∣ M) :
    lucasV P M = 2 := by
  classical
  have hp' : p.Prime := Fact.out
  have hD0 : (P ^ 2 - 4 : ZMod p) ≠ 0 := fun h => hD ⟨0, by rw [h]; ring⟩
  have hchar : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hDpow : (P ^ 2 - 4 : ZMod p) ^ (p / 2) = -1 := by
    have hdi := FiniteField.pow_dichotomy hchar hD0
    rw [ZMod.card] at hdi
    rcases hdi with h | h
    · exact absurd ((ZMod.euler_criterion p hD0).2 h) hD
    · exact h
  have hirr : Irreducible (X ^ 2 - C (P ^ 2 - 4 : ZMod p)) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two (fun b hb => hD ⟨b, by rw [← hb]; ring⟩)
  letI : Fact (Irreducible (X ^ 2 - C (P ^ 2 - 4 : ZMod p))) := ⟨hirr⟩
  letI : CharP (AdjoinRoot (X ^ 2 - C (P ^ 2 - 4 : ZMod p))) p :=
    charP_of_injective_algebraMap
      (algebraMap (ZMod p) (AdjoinRoot (X ^ 2 - C (P ^ 2 - 4 : ZMod p)))).injective p
  have hs2 : (AdjoinRoot.root (X ^ 2 - C (P ^ 2 - 4 : ZMod p))) ^ 2 =
      algebraMap (ZMod p) _ (P ^ 2 - 4) := by
    have h := AdjoinRoot.eval₂_root (X ^ 2 - C (P ^ 2 - 4 : ZMod p))
    simp only [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C, sub_eq_zero] at h
    exact h
  have hpodd : p = 2 * (p / 2) + 1 := by
    rcases hp'.eq_two_or_odd with h | h
    · exact absurd h hp2
    · omega
  have hsp : (AdjoinRoot.root (X ^ 2 - C (P ^ 2 - 4 : ZMod p))) ^ p =
      -(AdjoinRoot.root (X ^ 2 - C (P ^ 2 - 4 : ZMod p))) := by
    set s := AdjoinRoot.root (X ^ 2 - C (P ^ 2 - 4 : ZMod p))
    calc s ^ p = (s ^ 2) ^ (p / 2) * s := by rw [← pow_mul, ← pow_succ, ← hpodd]
      _ = algebraMap (ZMod p) _ ((P ^ 2 - 4 : ZMod p) ^ (p / 2)) * s := by rw [hs2, map_pow]
      _ = -s := by rw [hDpow]; simp
  exact lucasV_eq_two_aux hp2 (algebraMap (ZMod p) _)
    (algebraMap (ZMod p) (AdjoinRoot (X ^ 2 - C (P ^ 2 - 4 : ZMod p)))).injective P _ hs2 hsp hM

/-- Integer form of the `p + 1` gate: if the Legendre symbol of the discriminant
is `-1` and `(p + 1) ∣ M`, then `p ∣ V_M - 2`, so `p` divides the gcd computed by
the Williams method. -/
theorem dvd_lucasV_sub_two (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P : ℤ)
    (hD : legendreSym p (P ^ 2 - 4) = -1) {M : ℕ} (hM : (p + 1) ∣ M) :
    (p : ℤ) ∣ lucasV P M - 2 := by
  have hns : ¬ IsSquare ((P : ZMod p) ^ 2 - 4) := by
    have h := (legendreSym.eq_neg_one_iff p).mp hD
    intro hsq
    refine h ?_
    have hcast : (((P ^ 2 - 4 : ℤ) : ZMod p)) = (P : ZMod p) ^ 2 - 4 := by push_cast; ring
    rw [hcast]
    exact hsq
  have hmod : ((lucasV P M - 2 : ℤ) : ZMod p) = 0 := by
    have hmap := map_lucasV (Int.castRingHom (ZMod p)) P M
    push_cast
    rw [show ((lucasV P M : ℤ) : ZMod p) = lucasV ((P : ℤ) : ZMod p) M from hmap]
    rw [lucasV_eq_two_of_nonsquare_disc p hp2 _ hns hM]
    ring
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hmod

/-! ## 3. The `p - 1` half of the gate: a square discriminant degenerates -/

/-- If the discriminant `D = P² - 4` is a square mod the odd prime `p`, the two
conjugate roots of `x² - Px + 1` already live in `𝔽_p`. -/
lemma roots_of_disc_sqrt (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P t : ZMod p)
    (ht : t ^ 2 = P ^ 2 - 4) : ∃ a b : ZMod p, a * b = 1 ∧ a + b = P := by
  have hp' : p.Prime := Fact.out
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp' Nat.prime_two).mp h)
    simpa using h2
  have hc2 : (2 : ZMod p) * (2 : ZMod p)⁻¹ = 1 := mul_inv_cancel₀ h2ne
  refine ⟨(P + t) * (2 : ZMod p)⁻¹, (P - t) * (2 : ZMod p)⁻¹, ?_, ?_⟩
  · have h1 : (P + t) * (2 : ZMod p)⁻¹ * ((P - t) * (2 : ZMod p)⁻¹)
        = (P * P - t ^ 2) * ((2 : ZMod p)⁻¹ * (2 : ZMod p)⁻¹) := by ring
    rw [h1, ht]
    calc (P * P - (P ^ 2 - 4)) * ((2 : ZMod p)⁻¹ * (2 : ZMod p)⁻¹)
        = (2 * (2 : ZMod p)⁻¹) * (2 * (2 : ZMod p)⁻¹) := by ring
      _ = 1 := by rw [hc2]; ring
  · have h1 : (P + t) * (2 : ZMod p)⁻¹ + (P - t) * (2 : ZMod p)⁻¹
        = (2 * (2 : ZMod p)⁻¹) * P := by ring
    rw [h1, hc2, one_mul]

/-- **The `p - 1` half of the discriminant gate.** If the discriminant is a
*square* mod `p`, the two roots already live in `𝔽_p`, so their order divides
`p - 1` and the method needs `(p - 1) ∣ M` rather than `(p + 1) ∣ M`: it has
silently degenerated into the Pollard `p - 1` method. -/
theorem lucasV_eq_two_of_square_disc (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P t : ZMod p)
    (ht : t ^ 2 = P ^ 2 - 4) {M : ℕ} (hM : (p - 1) ∣ M) :
    lucasV P M = 2 := by
  obtain ⟨a, b, hab, hsum⟩ := roots_of_disc_sqrt p hp2 P t ht
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_mul] at hab
    exact zero_ne_one hab
  have hb0 : b ≠ 0 := by
    intro h
    rw [h, mul_zero] at hab
    exact zero_ne_one hab
  obtain ⟨k, rfl⟩ := hM
  refine lucasV_eq_two_of_pow_eq_one hab hsum ?_ ?_
  · rw [pow_mul, ZMod.pow_card_sub_one_eq_one ha0, one_pow]
  · rw [pow_mul, ZMod.pow_card_sub_one_eq_one hb0, one_pow]

/-- **Exact value at the `p + 1` step for a square discriminant.** When `D` is
a square mod `p` the Frobenius fixes both roots, so `V_{p+1} = P² - 2` — the
value `2` is attained only in the degenerate case `D = 0`. -/
theorem lucasV_p_add_one_of_square_disc (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P t : ZMod p)
    (ht : t ^ 2 = P ^ 2 - 4) : lucasV P (p + 1) = P ^ 2 - 2 := by
  obtain ⟨a, b, hab, hsum⟩ := roots_of_disc_sqrt p hp2 P t ht
  rw [lucasV_eq_pow_add_pow hab hsum, pow_succ, pow_succ, ZMod.pow_card, ZMod.pow_card]
  have h : a * a + b * b = (a + b) ^ 2 - 2 * (a * b) := by ring
  rw [h, hab, hsum]; ring

/-- **The discriminant gate, sharp form.** The `p + 1` congruence
`V_{p+1} ≡ 2 (mod p)` holds *exactly* when the discriminant is a non-residue
or vanishes. This is the formal content of the experimental identity
"per-base `p + 1` success rate `=` the `(D | p) = -1` rate": for a base with
`D ≠ 0` the method works at `p` if and only if `(D | p) = -1`. -/
theorem lucasV_p_add_one_eq_two_iff (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P : ZMod p) :
    lucasV P (p + 1) = 2 ↔ (¬ IsSquare (P ^ 2 - 4) ∨ P ^ 2 - 4 = 0) := by
  constructor
  · intro h
    by_cases hsq : IsSquare (P ^ 2 - 4)
    · right
      obtain ⟨r, hr⟩ := hsq
      have ht : r ^ 2 = P ^ 2 - 4 := by rw [hr]; ring
      have hval := lucasV_p_add_one_of_square_disc p hp2 P r ht
      rw [h] at hval
      linear_combination -hval
    · exact Or.inl hsq
  · rintro (h | h)
    · exact lucasV_eq_two_of_nonsquare_disc p hp2 P h dvd_rfl
    · have ht : (0 : ZMod p) ^ 2 = P ^ 2 - 4 := by rw [h]; ring
      rw [lucasV_p_add_one_of_square_disc p hp2 P 0 ht]
      linear_combination h

/-- In the split case the success criterion becomes an order condition inside
`𝔽_p^×` itself: there is a nonzero `a` with `V_M = 2 ↔ a^M = 1`. Since
`ord(a) ∣ p - 1`, no amount of `p + 1` smoothness helps once the gate is open. -/
theorem lucasV_eq_two_iff_of_square_disc (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P t : ZMod p)
    (ht : t ^ 2 = P ^ 2 - 4) :
    ∃ a : ZMod p, a ≠ 0 ∧ ∀ M : ℕ, (lucasV P M = 2 ↔ a ^ M = 1) := by
  obtain ⟨a, b, hab, hsum⟩ := roots_of_disc_sqrt p hp2 P t ht
  refine ⟨a, ?_, fun M => lucasV_eq_two_iff_pow_eq_one hab hsum M⟩
  intro h
  rw [h, zero_mul] at hab
  exact zero_ne_one hab

/-! ## 4. The gcd step returns the factor -/

/-- **The gcd step is exact.** If `p ∣ V` but `q ∤ V`, then `gcd(V, p·q) = p`:
the Williams method returns the factor `p` itself, never the trivial divisors. -/
theorem williams_gcd_eq_factor {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {V : ℤ}
    (hpV : (p : ℤ) ∣ V) (hqV : ¬ (q : ℤ) ∣ V) :
    Int.gcd V ((p * q : ℕ) : ℤ) = p := by
  have hpg : p ∣ Int.gcd V ((p * q : ℕ) : ℤ) :=
    Int.dvd_gcd hpV ⟨(q : ℤ), by push_cast; ring⟩
  have hgN : Int.gcd V ((p * q : ℕ) : ℤ) ∣ p * q := by
    have h : (Int.gcd V ((p * q : ℕ) : ℤ) : ℤ) ∣ ((p * q : ℕ) : ℤ) :=
      Int.gcd_dvd_right V ((p * q : ℕ) : ℤ)
    exact_mod_cast h
  obtain ⟨m, hm⟩ := hpg
  rw [hm] at hgN
  have hmq : m ∣ q := (mul_dvd_mul_iff_left hp.ne_zero).mp hgN
  have hgV : (Int.gcd V ((p * q : ℕ) : ℤ) : ℤ) ∣ V := Int.gcd_dvd_left V ((p * q : ℕ) : ℤ)
  rcases hq.eq_one_or_self_of_dvd m hmq with hm1 | hm1
  · rw [hm, hm1, mul_one]
  · exfalso
    refine hqV (dvd_trans ?_ hgV)
    rw [hm, hm1]
    exact ⟨(p : ℤ), by push_cast; ring⟩

/-! ## 5. Smoothness feeds the exponent: `p + 1` powersmooth ⇒ `(p+1) ∣ M` -/

-- [dropped: platform already declares lcmUpTo]
lemma lcmUpTo_ne_zero (B : ℕ) : lcmUpTo B ≠ 0 := by
  rw [lcmUpTo, Ne, Finset.lcm_eq_zero_iff]
  simp

/-- **Powersmoothness is exactly what the exponent needs.** If every prime
power `ℓ^{v_ℓ(n)}` exactly dividing `n` is at most `B` — a max-plus (tropical)
condition on the valuation vector of `n` — then `n ∣ lcm(1, …, B)`. Applied to
`n = p + 1` this is the hypothesis under which the Williams exponent reaches
the factor. -/
theorem dvd_lcmUpTo_of_powersmooth {n B : ℕ} (hn : n ≠ 0)
    (h : ∀ l : ℕ, l.Prime → l ^ (n.factorization l) ≤ B) : n ∣ lcmUpTo B := by
  rw [← Nat.factorization_le_iff_dvd hn (lcmUpTo_ne_zero B)]
  intro l
  by_cases hl : l.Prime
  · have hmem : l ^ (n.factorization l) ∈ Finset.Icc 1 B :=
      Finset.mem_Icc.mpr ⟨Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ hl.ne_zero), h l hl⟩
    exact (hl.pow_dvd_iff_le_factorization (lcmUpTo_ne_zero B)).mp (Finset.dvd_lcm hmem)
  · simp [Nat.factorization_eq_zero_of_not_prime n hl]

/-! ## 6. The degenerate base `P = 2` (`D = 0`) -/

/-- With base `P = 2` the discriminant vanishes and the Lucas sequence is
constant. -/
theorem lucasV_two_eq_two (n : ℕ) : lucasV (2 : ℤ) n = 2 := by
  induction n using Nat.twoStepInduction with
  | zero => rfl
  | one => rfl
  | more n ih1 ih2 => rw [lucasV_succ_succ, ih1, ih2]; ring

/-- **The degenerate base.** For `P = 2` the Williams gcd is always the whole
modulus, so the base `P = 2` can never split anything: this is the `D = 0`
degeneracy observed in the experiment. -/
theorem plusOne_base_two_degenerate (M N : ℕ) :
    Int.gcd (lucasV (2 : ℤ) M - 2) (N : ℤ) = N := by
  rw [lucasV_two_eq_two, sub_self]
  simp

/-- The discriminant vanishes exactly at the two degenerate bases `P = ±2`. -/
theorem disc_eq_zero_iff (P : ℤ) : P ^ 2 - 4 = 0 ↔ P = 2 ∨ P = -2 := by
  constructor
  · intro h
    have h' : (P - 2) * (P + 2) = 0 := by linarith [h]
    rcases mul_eq_zero.mp h' with h1 | h1
    · left; linarith
    · right; linarith
  · rintro (rfl | rfl) <;> ring

/-! ## 7. Bases 3 and 7 share a square class -/

/-- `D₇ = 45 = 5 · 3²` and `D₃ = 5` have the same Legendre symbol away from
`p = 3`. -/
theorem legendreSym_fortyfive_eq_five (p : ℕ) [Fact p.Prime] (hp3 : p ≠ 3) :
    legendreSym p 45 = legendreSym p 5 := by
  have h3ne : ((3 : ℤ) : ZMod p) ≠ 0 := by
    intro hdvd
    have h0 : ((3 : ℕ) : ZMod p) = 0 := by exact_mod_cast hdvd
    rw [ZMod.natCast_eq_zero_iff] at h0
    exact hp3 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp h0)
  have h9 : legendreSym p ((3 : ℤ) * 3) = 1 := by
    rw [legendreSym.mul, ← sq]
    exact legendreSym.sq_one p h3ne
  rw [show (45 : ℤ) = 5 * (3 * 3) by norm_num, legendreSym.mul, h9, mul_one]

/-- **Square-class invariance of the gate**, of which `D₃ = 5` versus
`D₇ = 45 = 5 · 3²` is the instance seen in the experiment: two bases whose
discriminants differ by a nonzero square factor are gated by the same
character, hence succeed on exactly the same primes. -/
theorem legendreSym_mul_sq (p : ℕ) [Fact p.Prime] (D c : ℤ) (hc : (c : ZMod p) ≠ 0) :
    legendreSym p (D * c ^ 2) = legendreSym p D := by
  have hsq : legendreSym p (c ^ 2) = 1 := by
    rw [sq, legendreSym.mul, ← sq]
    exact legendreSym.sq_one p hc
  rw [legendreSym.mul, hsq, mul_one]

end PlusOneWilliams
section
open PlusOneWilliams
open Polynomial

theorem solution (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (P : ℤ)
    (hD : legendreSym p (P ^ 2 - 4) = -1) {M : ℕ} (hM : (p + 1) ∣ M) :
    (p : ℤ) ∣ lucasV P M - 2 :=
  @PlusOneWilliams.dvd_lucasV_sub_two p _ hp2 P hD M hM

end
