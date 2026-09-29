-- Prove2me | solution 1 for EulerTwoSquares.gaussianInt_dvd_iff_cross
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T18:59:23.257844+00:00
-- url     : https://prove2.me/submissions/0a908caf-0107-4e82-8067-c06bbfc379ff

-- Sol generated from Algebra/EulerTwoSquaresGaussian.lean
import Mathlib

/-!
# The class bit is a Gaussian divisibility, and the two bits split `N` in `ℤ[i]`

The counting theorem of `EulerTwoSquaresCount` attaches to every representation
`a² + b² = p*q` a pair of bits

`(⟦p ∣ a*f - b*e⟧, ⟦q ∣ a*h - b*g⟧) ∈ Bool × Bool`,

where `p = e²+f²` and `q = g²+h²`.  That bit looks like an ad-hoc congruence.  This file
identifies it with a statement in the Gaussian integers `ℤ[i] = GaussianInt`:

`EulerTwoSquares.gaussianInt_dvd_iff_cross`:  `⟨e,f⟩ ∣ ⟨a,b⟩  ↔  (p : ℤ) ∣ a*f - b*e`.

So the bit records **which of the two conjugate Gaussian primes above `p` divides `a + b·i`**
— a Frobenius-style choice — and `EulerTwoSquares.gaussianInt_dvd_exactly_one` says exactly
one of `⟨e,f⟩`, `⟨e,-f⟩` does.  Finally `EulerTwoSquares.gaussianInt_split` exhibits the
resulting factorisation of `a + b·i` into a Gaussian prime above `p` and a Gaussian integer of
norm `q`, which is the structural reason the representation count is a power of two.

Everything here is elementary: the only inputs from `EulerTwoSquaresCount` are
`prime_dvd_cross_or` and `prime_not_dvd_cross_both`.
-/


variable {p q : ℕ}

/-- Multiplication of Gaussian integers in coordinates. -/
theorem gaussianInt_mk_mul (e f u v : ℤ) :
    (⟨e, f⟩ : GaussianInt) * ⟨u, v⟩ = ⟨e * u - f * v, e * v + f * u⟩ := by
  ext
  · simp; ring
  · simp

/-! ## From one divisibility to the other -/

/-- If `p` divides the cross term `a*f - b*e`, it also divides the dot term `a*e + b*f`.
Both are needed to build the Gaussian quotient. -/
theorem dvd_dot_of_dvd_cross (hp : p.Prime) {e f a b : ℤ}
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hab : a ^ 2 + b ^ 2 = (p : ℤ) * q)
    (hcross : (p : ℤ) ∣ a * f - b * e) : (p : ℤ) ∣ a * e + b * f := by
  obtain ⟨k, hk⟩ := hcross
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hsq : (a * e + b * f) ^ 2 = (p : ℤ) ^ 2 * ((q : ℤ) - k ^ 2) := by
    have hid : (a * e + b * f) ^ 2 + (a * f - b * e) ^ 2 = (a ^ 2 + b ^ 2) * (e ^ 2 + f ^ 2) := by
      ring
    rw [hk, hab, hef] at hid
    linear_combination hid
  refine hpZ.dvd_of_dvd_pow (n := 2) ⟨(p : ℤ) * ((q : ℤ) - k ^ 2), ?_⟩
  rw [hsq]; ring


/-! ## The bridge -/



/-! ## Exactly one Gaussian prime above `p` divides a given representation -/




theorem solution(hp : p.Prime) {e f a b : ℤ}
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hab : a ^ 2 + b ^ 2 = (p : ℤ) * q) :
    (⟨e, f⟩ : GaussianInt) ∣ ⟨a, b⟩ ↔ (p : ℤ) ∣ a * f - b * e := by
  constructor
  · rintro ⟨⟨u, v⟩, huv⟩
    rw [gaussianInt_mk_mul] at huv
    have hre : a = e * u - f * v := congrArg Zsqrtd.re huv
    have him : b = e * v + f * u := congrArg Zsqrtd.im huv
    exact ⟨-v, by rw [hre, him, ← hef]; ring⟩
  · intro hcross
    obtain ⟨v', hv'⟩ := hcross
    obtain ⟨u, hu⟩ := dvd_dot_of_dvd_cross (q := q) hp hef hab ⟨v', hv'⟩
    refine ⟨⟨u, -v'⟩, ?_⟩
    rw [gaussianInt_mk_mul]
    have hp0 : (p : ℤ) ≠ 0 := Int.natCast_ne_zero.2 hp.ne_zero
    have hre : (p : ℤ) * a = (p : ℤ) * (e * u - f * -v') := by
      calc (p : ℤ) * a = a * (e ^ 2 + f ^ 2) := by rw [hef]; ring
        _ = e * (a * e + b * f) + f * (a * f - b * e) := by ring
        _ = e * ((p : ℤ) * u) + f * ((p : ℤ) * v') := by rw [hu, hv']
        _ = (p : ℤ) * (e * u - f * -v') := by ring
    have him : (p : ℤ) * b = (p : ℤ) * (e * -v' + f * u) := by
      calc (p : ℤ) * b = b * (e ^ 2 + f ^ 2) := by rw [hef]; ring
        _ = f * (a * e + b * f) - e * (a * f - b * e) := by ring
        _ = f * ((p : ℤ) * u) - e * ((p : ℤ) * v') := by rw [hu, hv']
        _ = (p : ℤ) * (e * -v' + f * u) := by ring
    exact congrArg₂ Zsqrtd.mk (mul_left_cancel₀ hp0 hre) (mul_left_cancel₀ hp0 him)
