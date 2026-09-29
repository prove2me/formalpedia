-- Prove2me | solution 1 for EulerTwoSquares.prime_not_dvd_two_mul_parts
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:02:08.112728+00:00
-- url     : https://prove2.me/submissions/3b1d98a4-63a6-492f-9d21-b99dc63b5e51

-- Sol generated from Algebra/EulerTwoSquaresDeterminism.lean
import Mathlib

/-!
# Which prime does Euler's step extract?

`EulerTwoSquaresCore.euler_gcd_pair_factors` shows that the two gcd's produced by Euler's
combination step multiply to `p * q`.  It does **not** say which of the two gcd's is `p` and
which is `q`.  This file settles that question completely for the Brahmagupta pair.

Write `p = e² + f²`, `q = g² + h²` and form the two representations of `N = p*q`

`A = e*g + f*h`, `B = e*h - f*g`,  `C = e*g - f*h`, `D = e*h + f*g`,

so that `A² + B² = C² + D² = N`.  Then the two cross terms factor *exactly*:

`A*D - B*C = 2*e*f*q`  and  `A*D + B*C = 2*g*h*p`   (`cross_sub_factors`, `cross_add_factors`).

Since an odd prime `p = e²+f²` divides neither `2`, nor `e`, nor `f`, these identities pin the
gcd's down on the nose:

`gcd(A*D - B*C, N) = q`  and  `gcd(A*D + B*C, N) = p`   (`gcd_cross_sub_eq_q`,
`gcd_cross_add_eq_p`).

So the extraction is *deterministic*, not merely proper: the signed cross term of the
Brahmagupta pair always yields the prime whose representation was **not** used in the "twist".
Working with normalised (non-negative) parts, `|B|·|C| = |B*C|`, so which prime comes out is
governed purely by the sign of `B*C = (e*h - f*g)(e*g - f*h)`
(`gcd_cross_abs_eq_q_of_pos`, `gcd_cross_abs_eq_p_of_neg`).  This is the sharpest possible
form of the "extraction always works" face of the Euler campaign.
-/


variable {p q : ℕ}

/-! ## An odd prime that is a sum of two squares divides neither part -/

/-- If `p` is an odd prime and `p = e² + f²`, then `p` divides neither `e` nor `f`. -/
theorem prime_not_dvd_of_sq_add_sq (hp : p.Prime) {e f : ℤ} (hef : e ^ 2 + f ^ 2 = (p : ℤ)) :
    ¬ ((p : ℤ) ∣ e ∧ (p : ℤ) ∣ f) := by
  rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
  have hone : (p : ℤ) * (p * (x ^ 2 + y ^ 2)) = (p : ℤ) * 1 := by
    subst hx; subst hy; linear_combination hef
  have hp0 : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have h1 : (p : ℤ) * (x ^ 2 + y ^ 2) = 1 := mul_left_cancel₀ (by omega) hone
  have hdvd : (p : ℤ) ∣ 1 := ⟨_, h1.symm⟩
  have : (p : ℤ) ≤ 1 := Int.le_of_dvd one_pos hdvd
  have := hp.two_le
  omega



/-! ## The two cross terms factor exactly -/



/-! ## Deterministic extraction -/




/-! ## The normalised (non-negative) form: the sign of `B*C` decides -/




/-! ## Where the four parts sit

The same two Brahmagupta identities also locate the parts themselves, which is what feeds the
quartic search barrier of `EulerTwoSquaresBarrier`. -/







theorem solution(hp : p.Prime) (hp2 : p ≠ 2) {e f : ℤ}
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) : ¬ ((p : ℤ) ∣ 2 * e * f) := by
  intro hdvd
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hfe : (p : ℤ) ∣ e ∨ (p : ℤ) ∣ f := by
    rcases hpZ.2.2 _ _ hdvd with h | h
    · rcases hpZ.2.2 _ _ h with h2 | he
      · exfalso
        have : p ∣ 2 := by exact_mod_cast h2
        exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
      · exact Or.inl he
    · exact Or.inr h
  -- dividing one part forces dividing the other
  refine prime_not_dvd_of_sq_add_sq hp hef ?_
  rcases hfe with he | hf
  · refine ⟨he, hpZ.dvd_of_dvd_pow (n := 2) ?_⟩
    have hf2 : f ^ 2 = (p : ℤ) - e ^ 2 := by linarith
    rw [hf2]
    exact dvd_sub dvd_rfl (he.pow (by norm_num))
  · refine ⟨hpZ.dvd_of_dvd_pow (n := 2) ?_, hf⟩
    have he2 : e ^ 2 = (p : ℤ) - f ^ 2 := by linarith
    rw [he2]
    exact dvd_sub dvd_rfl (hf.pow (by norm_num))
