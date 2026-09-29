-- Prove2me | solution 1 for EulerTwoSquares.repFinset_card_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:09:02.459988+00:00
-- url     : https://prove2.me/submissions/a2259cef-2956-4baf-a67c-1835a78d45a4

import Mathlib
import Definitions.Def_Algebra_EulerTwoSquaresRepCount

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Algebra/EulerTwoSquaresCore.lean ====
/-!
# Euler's factorization method: the exact algebra of the combination step

Euler's factorisation method takes an integer `N` presented in **two essentially different
ways** as a sum of two squares,

`N = a² + b² = c² + d²`,

and extracts a nontrivial factor of `N` from the *cross term* `a*d - b*c`, namely
`gcd(a*d - b*c, N)`.  Conceptually the cross term is `Im (z₁ * conj z₂)` for the two Gaussian
integers `z₁ = a + b i`, `z₂ = c + d i` of norm `N`.

This file proves the algebraic core of the method, **unconditionally on any primality
assumption**:

* `EulerTwoSquares.rigidity` — the rigidity lemma: `a*d = b*c` together with
  `a*c + b*d = a² + b²` forces `(c,d) = (a,b)`.  This is the equality case of
  Cauchy–Schwarz over `ℤ`, proved by pure linear algebra.
* `EulerTwoSquares.not_dvd_cross` — `N` never divides the cross term unless the two
  representations coincide.
* `EulerTwoSquares.not_isCoprime_cross` — the cross term is never coprime to `N` unless the
  two representations coincide after a swap.
* `EulerTwoSquares.euler_gcd_proper` — **the main theorem**: for positive `a,b,c,d` with
  `a² + b² = c² + d² = N` and the two representations essentially distinct,
  `1 < gcd(a*d - b*c, N) < N`.  So Euler's extraction *always* produces a proper nontrivial
  divisor; no primality, no smoothness, no genericity hypothesis is needed.
* `EulerTwoSquares.euler_extraction_semiprime` — for `N = p*q` a product of two primes the
  extracted divisor is exactly `p` or `q`.
* `EulerTwoSquares.prime_rep_unique` — as an immediate corollary, a prime has an essentially
  unique representation as a sum of two squares.

The proofs use only the two Brahmagupta–Fibonacci identities and integrality; in particular
they do not use unique factorisation in `ℤ[i]`.
-/

namespace EulerTwoSquares

/-! ## The two Brahmagupta–Fibonacci identities -/

/-- Brahmagupta–Fibonacci, "minus" branch. -/
theorem brahmagupta_sub (a b c d : ℤ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 := by
  ring

/-- Brahmagupta–Fibonacci, "plus" branch. -/
theorem brahmagupta_add (a b c d : ℤ) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 := by
  ring

/-- The product of the two cross terms is a multiple of `a² + b²` whenever the two
representations have the same value: this is the divisibility that drives Euler's method. -/
theorem dvd_cross_mul_cross {a b c d : ℤ} (h : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2) :
    (a ^ 2 + b ^ 2) ∣ (a * d - b * c) * (a * d + b * c) :=
  ⟨a ^ 2 - c ^ 2, by linear_combination a ^ 2 * h⟩

/-! ## Rigidity: the equality case of Cauchy–Schwarz over `ℤ` -/

/-- **Rigidity.**  If the "imaginary part" `a*d - b*c` of `z₁ * conj z₂` vanishes and the
"real part" `a*c + b*d` attains the maximal value `a² + b²`, then `z₂ = z₁`.
Only `0 < a² + b²` is needed; no relation between the norms is assumed. -/
theorem rigidity {a b c d : ℤ} (hpos : 0 < a ^ 2 + b ^ 2) (hcross : a * d = b * c)
    (hdot : a * c + b * d = a ^ 2 + b ^ 2) : c = a ∧ d = b := by
  have hne : (a ^ 2 + b ^ 2) ≠ 0 := ne_of_gt hpos
  have hc : (a ^ 2 + b ^ 2) * c = (a ^ 2 + b ^ 2) * a := by
    linear_combination a * hdot - b * hcross
  have hca : c = a := mul_left_cancel₀ hne hc
  refine ⟨hca, ?_⟩
  rcases eq_or_ne b 0 with hb | hb
  · have ha : a ≠ 0 := by
      intro h; rw [h, hb] at hpos; simp at hpos
    have hd0 : a * d = 0 := by rw [hcross, hb]; ring
    have hdz := (mul_eq_zero.1 hd0).resolve_left ha
    rw [hdz, hb]
  · have hbd : b * d = b * b := by rw [hca] at hdot; linear_combination hdot
    exact mul_left_cancel₀ hb hbd

/-! ## The two failure modes are impossible -/

/-- The cross term is never divisible by `N` unless the two representations are literally
equal.  (Equivalently: `gcd(a*d - b*c, N) < N`.) -/
theorem not_dvd_cross {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2) (hne : ¬(c = a ∧ d = b)) :
    ¬ (a ^ 2 + b ^ 2) ∣ (a * d - b * c) := by
  intro hdvd
  set N : ℤ := a ^ 2 + b ^ 2 with hNdef
  have hNpos : 0 < N := by positivity
  have key : (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 = N ^ 2 := by
    have := brahmagupta_sub a b c d
    rw [hN] at this
    linarith [this]
  obtain ⟨k, hk⟩ := hdvd
  have hk2 : (a * c + b * d) ^ 2 + N ^ 2 * k ^ 2 = N ^ 2 := by
    rw [hk] at key; linarith [key, sq_nonneg (N * k)]
  have hdotpos : 0 < a * c + b * d := by positivity
  have hkzero : k = 0 := by
    by_contra hk0
    have h1 : 1 ≤ k ^ 2 := by
      rcases lt_or_gt_of_ne hk0 with h | h
      · nlinarith
      · nlinarith
    nlinarith [sq_nonneg (a * c + b * d)]
  have hcross : a * d = b * c := by
    have : a * d - b * c = 0 := by rw [hk, hkzero, mul_zero]
    linarith
  have hdot : a * c + b * d = N := by
    have h0 : (a * c + b * d) ^ 2 = N ^ 2 := by
      rw [hk, hkzero, mul_zero] at key; linarith
    nlinarith [hdotpos, hNpos]
  exact hne (rigidity hNpos hcross hdot)

/-- The *conjugate* cross term `a*d + b*c` is never divisible by `N` unless the two
representations agree after a swap.  (Equivalently: `gcd(a*d + b*c, N) < N`.) -/
theorem not_dvd_cross_add {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2) (hne : ¬(d = a ∧ c = b)) :
    ¬ (a ^ 2 + b ^ 2) ∣ (a * d + b * c) := by
  intro hdvd
  set N : ℤ := a ^ 2 + b ^ 2 with hNdef
  have hNpos : 0 < N := by positivity
  have key : (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = N ^ 2 := by
    have := brahmagupta_add a b c d
    rw [hN] at this
    linarith [this]
  have hpos : 0 < a * d + b * c := by positivity
  have hle : N ≤ a * d + b * c := Int.le_of_dvd hpos hdvd
  have hge : a * d + b * c ≤ N := by nlinarith [sq_nonneg (a * c - b * d)]
  have heq : a * d + b * c = N := le_antisymm hge hle
  have hz : a * c - b * d = 0 := by
    have hsq : (a * c - b * d) ^ 2 = 0 := by rw [heq] at key; linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
  exact hne (rigidity hNpos (by linarith) heq)

/-- The cross term is never coprime to `N` unless the two representations agree after a
swap.  (Equivalently: `1 < gcd(a*d - b*c, N)`.) -/
theorem not_isCoprime_cross {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2) (hne : ¬(d = a ∧ c = b)) :
    ¬ IsCoprime (a * d - b * c) (a ^ 2 + b ^ 2) := fun hcop =>
  not_dvd_cross_add ha hb hc hd hN hne
    ((hcop.symm).dvd_of_dvd_mul_left (dvd_cross_mul_cross hN))

/-- Dually, the conjugate cross term is never coprime to `N` unless the two representations
are literally equal. -/
theorem not_isCoprime_cross_add {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 < d) (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2) (hne : ¬(c = a ∧ d = b)) :
    ¬ IsCoprime (a * d + b * c) (a ^ 2 + b ^ 2) := fun hcop =>
  not_dvd_cross ha hb hc hd hN hne
    ((hcop.symm).dvd_of_dvd_mul_right (dvd_cross_mul_cross hN))

/-! ## Euler's extraction theorem -/

/-- **Euler's extraction theorem.**  If a positive integer `N` has two essentially distinct
representations `N = a² + b² = c² + d²` with all parts positive, then
`gcd(a*d - b*c, N)` is a *proper nontrivial* divisor of `N`.

The hypotheses are exactly "the two representations are essentially distinct": they are not
equal, and they are not equal after swapping the two squares. -/
theorem euler_gcd_proper {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2) (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b)) :
    1 < Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) ∧
      ((Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) : ℤ) < a ^ 2 + b ^ 2) := by
  set N : ℤ := a ^ 2 + b ^ 2 with hNdef
  have hNpos : 0 < N := by positivity
  set g : ℕ := Int.gcd (a * d - b * c) N with hg
  have hgdvdN : (g : ℤ) ∣ N := Int.gcd_dvd_right _ _
  have hgdvdc : (g : ℤ) ∣ (a * d - b * c) := Int.gcd_dvd_left _ _
  have hg1 : 1 < g := by
    rcases Nat.lt_or_ge 1 g with h | h
    · exact h
    · interval_cases g
      · exfalso
        have : N = 0 := by
          have := Int.gcd_eq_zero_iff.1 hg.symm
          exact this.2
        omega
      · exact absurd (Int.isCoprime_iff_gcd_eq_one.2 hg.symm)
          (not_isCoprime_cross ha hb hc hd hN hne2)
  refine ⟨hg1, ?_⟩
  rcases lt_or_eq_of_le (Int.le_of_dvd hNpos hgdvdN) with h | h
  · exact h
  · exfalso
    have hdvdN : N ∣ (a * d - b * c) := by rw [← h]; exact hgdvdc
    exact not_dvd_cross ha hb hc hd hN hne1 hdvdN

/-- **Uniqueness of the two-square representation of a prime.**  A direct corollary of
Euler's extraction theorem: a second essentially distinct representation would produce a
proper nontrivial divisor of the prime. -/
theorem prime_rep_unique {p : ℕ} (hp : p.Prime) {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b)
    (hc : 0 < c) (hd : 0 < d) (h1 : a ^ 2 + b ^ 2 = (p : ℤ)) (h2 : c ^ 2 + d ^ 2 = (p : ℤ)) :
    (c = a ∧ d = b) ∨ (d = a ∧ c = b) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hne1, hne2⟩ := hcon
  have hne1' : ¬(c = a ∧ d = b) := fun h => hne1 h.1 h.2
  have hne2' : ¬(d = a ∧ c = b) := fun h => hne2 h.1 h.2
  have hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2 := by rw [h1, h2]
  obtain ⟨hlow, hhigh⟩ := euler_gcd_proper ha hb hc hd hN hne1' hne2'
  set g : ℕ := Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) with hg
  have hgdvd : (g : ℤ) ∣ (a ^ 2 + b ^ 2) := Int.gcd_dvd_right _ _
  rw [h1] at hgdvd hhigh
  have : g ∣ p := by exact_mod_cast hgdvd
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp g this) with h | h
  · omega
  · rw [h] at hhigh; simp at hhigh

/-- Divisors of a product of two primes. -/
theorem eq_of_dvd_prime_mul_prime {p q g : ℕ} (hp : p.Prime) (hq : q.Prime) (hg : g ∣ p * q)
    (h1 : 1 < g) (h2 : g < p * q) : g = p ∨ g = q := by
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp (Nat.gcd g p) (Nat.gcd_dvd_right g p)) with hk | hk
  · -- `g` is coprime to `p`, hence divides `q`
    have hcop : Nat.Coprime g p := hk
    have : g ∣ q := (Nat.Coprime.dvd_of_dvd_mul_left hcop hg)
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq g this) with h | h
    · omega
    · exact Or.inr h
  · -- `p ∣ g`
    have hpg : p ∣ g := hk ▸ Nat.gcd_dvd_left g p
    obtain ⟨m, hm⟩ := hpg
    have hmq : m ∣ q := by
      have : p * m ∣ p * q := hm ▸ hg
      exact (mul_dvd_mul_iff_left hp.pos.ne').1 this
    rcases (Nat.Prime.eq_one_or_self_of_dvd hq m hmq) with h | h
    · left; rw [hm, h, mul_one]
    · exfalso; rw [h] at hm; omega

/-- **Euler's method on a semiprime.**  Two essentially distinct representations of `N = p*q`
(`p`, `q` prime) produce, via a single gcd, one of the two prime factors. -/
theorem euler_extraction_semiprime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) {a b c d : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a ^ 2 + b ^ 2 = (p * q : ℕ)) (h2 : c ^ 2 + d ^ 2 = (p * q : ℕ))
    (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b)) :
    Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) = p ∨
      Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) = q := by
  have hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2 := by rw [h1, h2]
  obtain ⟨hlow, hhigh⟩ := euler_gcd_proper ha hb hc hd hN hne1 hne2
  set g : ℕ := Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) with hg
  have hgdvd : (g : ℤ) ∣ (a ^ 2 + b ^ 2) := Int.gcd_dvd_right _ _
  rw [h1] at hgdvd hhigh
  have hgN : g ∣ p * q := by exact_mod_cast hgdvd
  have hlt : g < p * q := by exact_mod_cast hhigh
  exact eq_of_dvd_prime_mul_prime hp hq hgN hlow hlt

/-- The conjugate form of Euler's extraction theorem: `gcd(a*d + b*c, N)` is also a proper
nontrivial divisor of `N`. -/
theorem euler_gcd_proper_add {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2) (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b)) :
    1 < Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) ∧
      ((Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) : ℤ) < a ^ 2 + b ^ 2) := by
  set N : ℤ := a ^ 2 + b ^ 2 with hNdef
  have hNpos : 0 < N := by positivity
  set g : ℕ := Int.gcd (a * d + b * c) N with hg
  have hgdvdN : (g : ℤ) ∣ N := Int.gcd_dvd_right _ _
  have hgdvdc : (g : ℤ) ∣ (a * d + b * c) := Int.gcd_dvd_left _ _
  have hg1 : 1 < g := by
    rcases Nat.lt_or_ge 1 g with h | h
    · exact h
    · interval_cases g
      · exfalso
        have hz : N = 0 := (Int.gcd_eq_zero_iff.1 hg.symm).2
        omega
      · exact absurd (Int.isCoprime_iff_gcd_eq_one.2 hg.symm)
          (not_isCoprime_cross_add ha hb hc hd hN hne1)
  refine ⟨hg1, ?_⟩
  rcases lt_or_eq_of_le (Int.le_of_dvd hNpos hgdvdN) with h | h
  · exact h
  · exfalso
    have hdvdN : N ∣ (a * d + b * c) := by rw [← h]; exact hgdvdc
    exact not_dvd_cross_add ha hb hc hd hN hne2 hdvdN

/-- **The two gcds recover the whole factorisation.**  For `N = p*q` a product of two distinct
primes, the two cross terms of a pair of essentially distinct representations produce the two
prime factors: `gcd(a*d - b*c, N) * gcd(a*d + b*c, N) = p*q`. -/
theorem euler_gcd_pair_factors {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {a b c d : ℤ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h1 : a ^ 2 + b ^ 2 = (p * q : ℕ)) (h2 : c ^ 2 + d ^ 2 = (p * q : ℕ))
    (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b)) :
    Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) * Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) = p * q := by
  have hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2 := by rw [h1, h2]
  have hg1 := euler_extraction_semiprime hp hq ha hb hc hd h1 h2 hne1 hne2
  -- the conjugate gcd is also `p` or `q`
  have hg2 : Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) = p ∨
      Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) = q := by
    obtain ⟨hlow, hhigh⟩ := euler_gcd_proper_add ha hb hc hd hN hne1 hne2
    set g₂ : ℕ := Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) with hg₂
    have hgdvd : (g₂ : ℤ) ∣ (a ^ 2 + b ^ 2) := Int.gcd_dvd_right _ _
    rw [h1] at hgdvd hhigh
    exact eq_of_dvd_prime_mul_prime hp hq (by exact_mod_cast hgdvd) hlow (by exact_mod_cast hhigh)
  -- `N` divides the product of the two cross terms, so each prime divides one of the gcds
  have hprod : (a ^ 2 + b ^ 2) ∣ (a * d - b * c) * (a * d + b * c) := dvd_cross_mul_cross hN
  have key : ∀ r : ℕ, r.Prime → (r : ℤ) ∣ (a ^ 2 + b ^ 2) →
      r ∣ Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) ∨
        r ∣ Int.gcd (a * d + b * c) (a ^ 2 + b ^ 2) := by
    intro r hr hrN
    have hri : Prime (r : ℤ) := Nat.prime_iff_prime_int.mp hr
    rcases hri.2.2 _ _ (hrN.trans hprod) with h | h
    · left
      exact_mod_cast Int.dvd_gcd h hrN
    · right
      exact_mod_cast Int.dvd_gcd h hrN
  have hpN : (p : ℤ) ∣ (a ^ 2 + b ^ 2) := by rw [h1]; exact_mod_cast Dvd.intro q rfl
  have hqN : (q : ℤ) ∣ (a ^ 2 + b ^ 2) := by rw [h1]; exact_mod_cast Dvd.intro_left p rfl
  have hpdvd := key p hp hpN
  have hqdvd := key q hq hqN
  rcases hg1 with e1 | e1
  · rcases hg2 with e2 | e2
    · exfalso
      rcases hqdvd with hqd | hqd
      · rw [e1] at hqd; exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 hqd).symm
      · rw [e2] at hqd; exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 hqd).symm
    · rw [e1, e2]
  · rcases hg2 with e2 | e2
    · rw [e1, e2]; exact Nat.mul_comm q p
    · exfalso
      rcases hpdvd with hpd | hpd
      · rw [e1] at hpd; exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hpd)
      · rw [e2] at hpd; exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 hpd)

/-! ## The degenerate boundary: representations with a zero part

Nothing in Euler's method really needs the parts to be strictly positive.  The only place
positivity was used above is the strict Cauchy–Schwarz step `0 < a*c + b*d`, and that step
survives on the boundary of the cone: if a scalar product degenerates then the two
representations are supported on complementary coordinates, which is exactly what the
essential-distinctness hypotheses forbid.  (Example: `25 = 5² + 0² = 3² + 4²`,
`gcd(5*4 - 0*3, 25) = 5`.) -/

/-- On the closed cone, the scalar product `a*c + b*d` of two essentially distinct
representations is still strictly positive. -/
theorem dot_pos_of_essentially_distinct {a b c d : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hNpos : 0 < a ^ 2 + b ^ 2) (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2)
    (hne2 : ¬(d = a ∧ c = b)) : 0 < a * c + b * d := by
  rcases lt_or_eq_of_le (by positivity : (0 : ℤ) ≤ a * c + b * d) with h | h
  · exact h
  exfalso
  have hac : a * c = 0 := by nlinarith [mul_nonneg ha hc, mul_nonneg hb hd]
  have hbd : b * d = 0 := by nlinarith [mul_nonneg ha hc, mul_nonneg hb hd]
  rcases mul_eq_zero.1 hac with ha0 | hc0
  · rcases mul_eq_zero.1 hbd with hb0 | hd0
    · rw [ha0, hb0] at hNpos; simp at hNpos
    · -- `a = 0`, `d = 0`: then `c² = b²` and the two representations are swaps
      have hcb : c = b := by
        have hfac : (c - b) * (c + b) = 0 := by rw [ha0, hd0] at hN; linarith
        rcases mul_eq_zero.1 hfac with h1 | h1
        · linarith
        · have : c = 0 := by linarith
          have : b = 0 := by linarith
          omega
      exact hne2 ⟨by rw [hd0, ha0], hcb⟩
  · rcases mul_eq_zero.1 hbd with hb0 | hd0
    · -- `c = 0`, `b = 0`: then `d² = a²`
      have hda : d = a := by
        have hfac : (d - a) * (d + a) = 0 := by rw [hc0, hb0] at hN; linarith
        rcases mul_eq_zero.1 hfac with h1 | h1
        · linarith
        · have : d = 0 := by linarith
          have : a = 0 := by linarith
          omega
      exact hne2 ⟨hda, by rw [hc0, hb0]⟩
    · rw [hc0, hd0] at hN; simp at hN; omega

/-- On the closed cone, the conjugate cross term `a*d + b*c` of two essentially distinct
representations is still strictly positive. -/
theorem cross_add_pos_of_essentially_distinct {a b c d : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) (hd : 0 ≤ d) (hNpos : 0 < a ^ 2 + b ^ 2) (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2)
    (hne1 : ¬(c = a ∧ d = b)) : 0 < a * d + b * c := by
  rcases lt_or_eq_of_le (by positivity : (0 : ℤ) ≤ a * d + b * c) with h | h
  · exact h
  exfalso
  have had : a * d = 0 := by nlinarith [mul_nonneg ha hd, mul_nonneg hb hc]
  have hbc : b * c = 0 := by nlinarith [mul_nonneg ha hd, mul_nonneg hb hc]
  rcases mul_eq_zero.1 had with ha0 | hd0
  · rcases mul_eq_zero.1 hbc with hb0 | hc0
    · rw [ha0, hb0] at hNpos; simp at hNpos
    · -- `a = 0`, `c = 0`: then `d² = b²`
      have hdb : d = b := by
        have hfac : (d - b) * (d + b) = 0 := by rw [ha0, hc0] at hN; linarith
        rcases mul_eq_zero.1 hfac with h1 | h1
        · linarith
        · have : d = 0 := by linarith
          have : b = 0 := by linarith
          omega
      exact hne1 ⟨by rw [hc0, ha0], hdb⟩
  · rcases mul_eq_zero.1 hbc with hb0 | hc0
    · -- `d = 0`, `b = 0`: then `c² = a²`
      have hca : c = a := by
        have hfac : (c - a) * (c + a) = 0 := by rw [hd0, hb0] at hN; linarith
        rcases mul_eq_zero.1 hfac with h1 | h1
        · linarith
        · have : c = 0 := by linarith
          have : a = 0 := by linarith
          omega
      exact hne1 ⟨hca, by rw [hd0, hb0]⟩
    · rw [hc0, hd0] at hN; simp at hN; omega

/-- The cross term is not divisible by `N`, on the closed cone. -/
theorem not_dvd_cross_nonneg {a b c d : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hNpos : 0 < a ^ 2 + b ^ 2) (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2)
    (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b)) :
    ¬ (a ^ 2 + b ^ 2) ∣ (a * d - b * c) := by
  intro hdvd
  set N : ℤ := a ^ 2 + b ^ 2 with hNdef
  have hdotpos : 0 < a * c + b * d :=
    dot_pos_of_essentially_distinct ha hb hc hd hNpos hN hne2
  have key : (a * c + b * d) ^ 2 + (a * d - b * c) ^ 2 = N ^ 2 := by
    have hbr := brahmagupta_sub a b c d
    rw [hN] at hbr
    linarith [hbr]
  obtain ⟨k, hk⟩ := hdvd
  have hkzero : k = 0 := by
    by_contra hk0
    have h1 : 1 ≤ k ^ 2 := by
      rcases lt_or_gt_of_ne hk0 with h | h
      · nlinarith
      · nlinarith
    rw [hk] at key
    nlinarith [sq_nonneg (a * c + b * d)]
  have hcross : a * d = b * c := by
    have hz : a * d - b * c = 0 := by rw [hk, hkzero, mul_zero]
    linarith
  have hdot : a * c + b * d = N := by
    have h0 : (a * c + b * d) ^ 2 = N ^ 2 := by
      rw [hk, hkzero, mul_zero] at key; linarith
    nlinarith [hdotpos, hNpos]
  exact hne1 (rigidity hNpos hcross hdot)

/-- The conjugate cross term is not divisible by `N`, on the closed cone. -/
theorem not_dvd_cross_add_nonneg {a b c d : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hNpos : 0 < a ^ 2 + b ^ 2) (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2)
    (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b)) :
    ¬ (a ^ 2 + b ^ 2) ∣ (a * d + b * c) := by
  intro hdvd
  set N : ℤ := a ^ 2 + b ^ 2 with hNdef
  have hpos : 0 < a * d + b * c :=
    cross_add_pos_of_essentially_distinct ha hb hc hd hNpos hN hne1
  have key : (a * c - b * d) ^ 2 + (a * d + b * c) ^ 2 = N ^ 2 := by
    have hbr := brahmagupta_add a b c d
    rw [hN] at hbr
    linarith [hbr]
  have hle : N ≤ a * d + b * c := Int.le_of_dvd hpos hdvd
  have hge : a * d + b * c ≤ N := by nlinarith [sq_nonneg (a * c - b * d)]
  have heq : a * d + b * c = N := le_antisymm hge hle
  have hz : a * c - b * d = 0 := by
    have hsq : (a * c - b * d) ^ 2 = 0 := by rw [heq] at key; linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hsq
  exact hne2 (rigidity hNpos (by linarith) heq)

/-- **Euler's extraction theorem on the closed cone.**  The parts of the two representations
need only be non-negative: essential distinctness alone forces `gcd(a*d - b*c, N)` to be a
proper nontrivial divisor of `N`. -/
theorem euler_gcd_proper_nonneg {a b c d : ℤ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hNpos : 0 < a ^ 2 + b ^ 2) (hN : c ^ 2 + d ^ 2 = a ^ 2 + b ^ 2)
    (hne1 : ¬(c = a ∧ d = b)) (hne2 : ¬(d = a ∧ c = b)) :
    1 < Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) ∧
      ((Int.gcd (a * d - b * c) (a ^ 2 + b ^ 2) : ℤ) < a ^ 2 + b ^ 2) := by
  set N : ℤ := a ^ 2 + b ^ 2 with hNdef
  set g : ℕ := Int.gcd (a * d - b * c) N with hg
  have hgdvdN : (g : ℤ) ∣ N := Int.gcd_dvd_right _ _
  have hgdvdc : (g : ℤ) ∣ (a * d - b * c) := Int.gcd_dvd_left _ _
  have hg1 : 1 < g := by
    rcases Nat.lt_or_ge 1 g with h | h
    · exact h
    · interval_cases g
      · exfalso
        have hz : N = 0 := (Int.gcd_eq_zero_iff.1 hg.symm).2
        omega
      · exfalso
        have hcop : IsCoprime (a * d - b * c) N := Int.isCoprime_iff_gcd_eq_one.2 hg.symm
        exact not_dvd_cross_add_nonneg ha hb hc hd hNpos hN hne1 hne2
          ((hcop.symm).dvd_of_dvd_mul_left (dvd_cross_mul_cross hN))
  refine ⟨hg1, ?_⟩
  rcases lt_or_eq_of_le (Int.le_of_dvd hNpos hgdvdN) with h | h
  · exact h
  · exfalso
    have hdvdN : N ∣ (a * d - b * c) := by rw [← h]; exact hgdvdc
    exact not_dvd_cross_nonneg ha hb hc hd hNpos hN hne1 hne2 hdvdN

end EulerTwoSquares
-- ==== upstream: Packages/Catalog/Algebra/EulerTwoSquaresCount.lean ====
/-!
# The eligibility class of Euler's method: exactly two representations, or none

Euler's factorisation method needs **two essentially distinct** representations of `N` as a
sum of two squares.  For `N = p*q` a product of two distinct odd primes this file settles
exactly when such a pair exists, and how many representations there are:

* `EulerTwoSquares.exactly_two_reps` — if `p ≠ q` are primes with `p ≡ q ≡ 1 [MOD 4]`, then
  `p*q` has **exactly two** essentially distinct representations as a sum of two positive
  squares: there are explicit `A,B,C,D` such that the ordered positive representations are
  precisely `(A,B), (B,A), (C,D), (D,C)`.
* `EulerTwoSquares.no_rep_of_three_mod_four` — if some prime `r ≡ 3 [MOD 4]` divides `n`
  exactly once, then `n` has **no** representation at all.  This kills the classes
  `(1,3), (3,1), (3,3)` and `(2,3)` of the semiprime table.
* `EulerTwoSquares.euler_works_iff_both_one_mod_four` — the resulting dichotomy for
  `N = p*q` with `p ≠ q` odd primes: two essentially distinct representations exist iff both
  primes are `1 mod 4`.

The "at most two" half is proved by a *class argument* powered by the extraction theorem of
`EulerTwoSquaresCore`: fixing representations `p = e²+f²` and `q = g²+h²`, every
representation `(a,b)` of `p*q` gets a pair of bits

`(⟦p ∣ a f - b e⟧, ⟦q ∣ a h - b g⟧) ∈ Bool × Bool`,

two representations with the same bits have `N ∣ a₁b₂ - a₂b₁`, and then
`EulerTwoSquares.not_dvd_cross` forces them to be equal.  Since `Bool × Bool` has four
elements there are at most four ordered representations, i.e. at most two up to order — and
the Brahmagupta construction produces four.  So the count is exact.
-/

namespace EulerTwoSquares

set_option synthInstance.maxSize 1000 in
set_option synthInstance.maxHeartbeats 1000000 in
/-- Five pairwise distinct elements of `Bool × Bool` cannot exist. -/
theorem pigeonhole_four_classes :
    ∀ v₁ v₂ v₃ v₄ v₅ : Bool × Bool, v₁ ≠ v₂ → v₁ ≠ v₃ → v₁ ≠ v₄ → v₁ ≠ v₅ → v₂ ≠ v₃ →
      v₂ ≠ v₄ → v₂ ≠ v₅ → v₃ ≠ v₄ → v₃ ≠ v₅ → v₄ ≠ v₅ → False := by decide

/-! ## Elementary facts about representations of a prime -/

/-- A prime is not a perfect square. -/
theorem prime_ne_sq {p b : ℕ} (hp : p.Prime) : p ≠ b ^ 2 := by
  intro h
  have hb : b ∣ p := ⟨b, by rw [h]; ring⟩
  rcases hp.eq_one_or_self_of_dvd b hb with h1 | h1
  · rw [h1] at h; simp at h; exact absurd h hp.one_lt.ne'
  · rw [h1] at h; nlinarith [hp.two_le]

/-- Both parts of a two-square representation of a prime are positive. -/
theorem prime_rep_pos {p : ℕ} (hp : p.Prime) {a b : ℕ} (h : a ^ 2 + b ^ 2 = p) :
    0 < a ∧ 0 < b := by
  constructor
  · rcases Nat.eq_zero_or_pos a with ha | ha
    · exact absurd (by rw [ha] at h; simpa using h.symm) (prime_ne_sq (b := b) hp)
    · exact ha
  · rcases Nat.eq_zero_or_pos b with hb | hb
    · exact absurd (by rw [hb] at h; simpa using h.symm) (prime_ne_sq (b := a) hp)
    · exact hb

/-- A prime `p ≡ 1 [MOD 4]` is a sum of two *distinct* positive squares. -/
theorem exists_prime_rep {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) :
    ∃ e f : ℤ, 0 < e ∧ 0 < f ∧ e ≠ f ∧ e ^ 2 + f ^ 2 = (p : ℤ) := by
  haveI := Fact.mk hp
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
  obtain ⟨ha, hb⟩ := prime_rep_pos hp hab
  refine ⟨(a : ℤ), (b : ℤ), by exact_mod_cast ha, by exact_mod_cast hb, ?_, by exact_mod_cast hab⟩
  intro hEq
  have hab' : a = b := by exact_mod_cast hEq
  subst hab'
  have h2 : 2 ∣ p := ⟨a ^ 2, by omega⟩
  have : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2
  omega

/-- A prime does not divide either part of one of its two-square representations. -/
theorem prime_not_dvd_part {p : ℕ} {e f : ℤ} (he : 0 < e) (hf : 0 < f)
    (h : e ^ 2 + f ^ 2 = (p : ℤ)) : ¬ ((p : ℤ) ∣ e) := by
  intro hdvd
  have hlt : e < (p : ℤ) := by nlinarith
  have := Int.le_of_dvd he hdvd
  omega

/-! ## The class bits attached to a representation -/

variable {p q : ℕ}

/-- For a representation `p = e² + f²` and a representation `a² + b² = p*q`, the prime `p`
divides one of the two "cross terms" `a f ∓ b e`. -/
theorem prime_dvd_cross_or (hp : p.Prime) {e f a b : ℤ}
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hab : a ^ 2 + b ^ 2 = (p : ℤ) * q) :
    (p : ℤ) ∣ (a * f - b * e) ∨ (p : ℤ) ∣ (a * f + b * e) := by
  have hprod : (p : ℤ) ∣ (a * f - b * e) * (a * f + b * e) :=
    ⟨f ^ 2 * q - b ^ 2, by linear_combination f ^ 2 * hab - b ^ 2 * hef⟩
  exact (Nat.prime_iff_prime_int.mp hp).2.2 _ _ hprod

/-- ... and it divides exactly one of them. -/
theorem prime_not_dvd_cross_both (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hp4 : p % 4 = 1)
    {e f a b : ℤ} (he : 0 < e) (hf : 0 < f)
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hab : a ^ 2 + b ^ 2 = (p : ℤ) * q) :
    ¬ ((p : ℤ) ∣ (a * f - b * e) ∧ (p : ℤ) ∣ (a * f + b * e)) := by
  rintro ⟨h1, h2⟩
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpe : ¬ ((p : ℤ) ∣ e) := prime_not_dvd_part he hf hef
  have hpf : ¬ ((p : ℤ) ∣ f) := prime_not_dvd_part hf he (by linarith)
  have hp2 : ¬ ((p : ℤ) ∣ 2) := by
    intro hd
    have h' : (p : ℤ) ≤ 2 := Int.le_of_dvd (by norm_num) hd
    have h'' : p ≤ 2 := by exact_mod_cast h'
    have := hp.two_le
    omega
  have h2af : (p : ℤ) ∣ 2 * (a * f) := by
    have hrw : 2 * (a * f) = (a * f - b * e) + (a * f + b * e) := by ring
    rw [hrw]; exact dvd_add h1 h2
  have h2be : (p : ℤ) ∣ 2 * (b * e) := by
    have hrw : 2 * (b * e) = (a * f + b * e) - (a * f - b * e) := by ring
    rw [hrw]; exact dvd_sub h2 h1
  have ha : (p : ℤ) ∣ a :=
    (hpi.dvd_mul.1 ((hpi.dvd_mul.1 h2af).resolve_left hp2)).resolve_right hpf
  have hb : (p : ℤ) ∣ b :=
    (hpi.dvd_mul.1 ((hpi.dvd_mul.1 h2be).resolve_left hp2)).resolve_right hpe
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have hpne : (p : ℤ) ≠ 0 := by
    have := hp.two_le; positivity
  have hcancel : (p : ℤ) * ((p : ℤ) * (a' ^ 2 + b' ^ 2)) = (p : ℤ) * (q : ℤ) := by
    linear_combination hab
  have hq' : (p : ℤ) * (a' ^ 2 + b' ^ 2) = (q : ℤ) := mul_left_cancel₀ hpne hcancel
  have hpdq : (p : ℤ) ∣ (q : ℤ) := ⟨a' ^ 2 + b' ^ 2, hq'.symm⟩
  have : p ∣ q := by exact_mod_cast hpdq
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 this)

/-- Two representations of `p*q` with the same `p`-bit satisfy `p ∣ a₁b₂ - a₂b₁`. -/
theorem cross_dvd_of_same_class (hp : p.Prime) {e f a₁ b₁ a₂ b₂ : ℤ} (he : 0 < e) (hf : 0 < f)
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hr1 : a₁ ^ 2 + b₁ ^ 2 = (p : ℤ) * q)
    (hr2 : a₂ ^ 2 + b₂ ^ 2 = (p : ℤ) * q)
    (hsame : ((p : ℤ) ∣ (a₁ * f - b₁ * e)) ↔ ((p : ℤ) ∣ (a₂ * f - b₂ * e))) :
    (p : ℤ) ∣ (a₁ * b₂ - a₂ * b₁) := by
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hpf : ¬ ((p : ℤ) ∣ f) := prime_not_dvd_part hf he (by linarith)
  have key : (p : ℤ) ∣ (a₁ * b₂ - a₂ * b₁) * f := by
    by_cases h1 : (p : ℤ) ∣ (a₁ * f - b₁ * e)
    · have h2 := hsame.1 h1
      have hrw : (a₁ * b₂ - a₂ * b₁) * f = b₂ * (a₁ * f - b₁ * e) - b₁ * (a₂ * f - b₂ * e) := by
        ring
      rw [hrw]; exact dvd_sub (h1.mul_left b₂) (h2.mul_left b₁)
    · have h2 : ¬ ((p : ℤ) ∣ (a₂ * f - b₂ * e)) := fun hh => h1 (hsame.2 hh)
      have h1' := (prime_dvd_cross_or (q := q) hp hef hr1).resolve_left h1
      have h2' := (prime_dvd_cross_or (q := q) hp hef hr2).resolve_left h2
      have hrw : (a₁ * b₂ - a₂ * b₁) * f = b₂ * (a₁ * f + b₁ * e) - b₁ * (a₂ * f + b₂ * e) := by
        ring
      rw [hrw]; exact dvd_sub (h1'.mul_left b₂) (h2'.mul_left b₁)
  exact (hpi.dvd_mul.1 key).resolve_right hpf

/-- **Injectivity of the class map.**  Two positive representations of `p*q` carrying the same
pair of class bits are equal. -/
theorem rep_eq_of_same_classes (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {e f g h a₁ b₁ a₂ b₂ : ℤ} (he : 0 < e) (hf : 0 < f) (hg : 0 < g) (hh : 0 < h)
    (hef : e ^ 2 + f ^ 2 = (p : ℤ)) (hgh : g ^ 2 + h ^ 2 = (q : ℤ))
    (ha₁ : 0 < a₁) (hb₁ : 0 < b₁) (ha₂ : 0 < a₂) (hb₂ : 0 < b₂)
    (hr1 : a₁ ^ 2 + b₁ ^ 2 = (p : ℤ) * q) (hr2 : a₂ ^ 2 + b₂ ^ 2 = (p : ℤ) * q)
    (hsp : ((p : ℤ) ∣ (a₁ * f - b₁ * e)) ↔ ((p : ℤ) ∣ (a₂ * f - b₂ * e)))
    (hsq : ((q : ℤ) ∣ (a₁ * h - b₁ * g)) ↔ ((q : ℤ) ∣ (a₂ * h - b₂ * g))) :
    a₂ = a₁ ∧ b₂ = b₁ := by
  have hdp : (p : ℤ) ∣ (a₁ * b₂ - a₂ * b₁) :=
    cross_dvd_of_same_class (q := q) hp he hf hef hr1 hr2 hsp
  have hr1' : a₁ ^ 2 + b₁ ^ 2 = (q : ℤ) * p := by rw [hr1]; ring
  have hr2' : a₂ ^ 2 + b₂ ^ 2 = (q : ℤ) * p := by rw [hr2]; ring
  have hdq : (q : ℤ) ∣ (a₁ * b₂ - a₂ * b₁) :=
    cross_dvd_of_same_class (q := p) hq hg hh hgh hr1' hr2' hsq
  have hcop : IsCoprime ((p : ℤ)) ((q : ℤ)) := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    simpa using (Nat.coprime_primes hp hq).2 hpq
  have hdvd : ((p : ℤ) * q) ∣ (a₁ * b₂ - a₂ * b₁) := hcop.mul_dvd hdp hdq
  by_contra hcon
  have hN : a₂ ^ 2 + b₂ ^ 2 = a₁ ^ 2 + b₁ ^ 2 := by rw [hr1, hr2]
  refine not_dvd_cross ha₁ hb₁ ha₂ hb₂ hN hcon ?_
  rw [hr1]
  have hrw : a₁ * b₂ - b₁ * a₂ = a₁ * b₂ - a₂ * b₁ := by ring
  rw [hrw]
  exact hdvd

/-! ## The Brahmagupta construction: four ordered representations -/

/-- A product of two distinct primes is never a perfect square. -/
theorem prime_mul_prime_ne_sq (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {A : ℤ} :
    A ^ 2 ≠ (p : ℤ) * q := by
  intro hA
  have hpi : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvd : (p : ℤ) ∣ A ^ 2 := ⟨(q : ℤ), hA⟩
  have hpA : (p : ℤ) ∣ A := hpi.dvd_of_dvd_pow hdvd
  obtain ⟨k, rfl⟩ := hpA
  have hpne : (p : ℤ) ≠ 0 := by have := hp.two_le; positivity
  have hcancel : (p : ℤ) * ((p : ℤ) * k ^ 2) = (p : ℤ) * (q : ℤ) := by linear_combination hA
  have hq' : (p : ℤ) * k ^ 2 = (q : ℤ) := mul_left_cancel₀ hpne hcancel
  have hpdq : (p : ℤ) ∣ (q : ℤ) := ⟨k ^ 2, hq'.symm⟩
  have : p ∣ q := by exact_mod_cast hpdq
  exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 this)

/-- The Brahmagupta–Fibonacci construction applied to representations of `p` and `q`
produces four pairwise distinct ordered representations of `p*q`. -/
theorem exists_four_reps (hp : p.Prime) (hq : q.Prime) (hp4 : p % 4 = 1) (hq4 : q % 4 = 1)
    (hpq : p ≠ q) :
    ∃ e f g h A B C D : ℤ,
      (0 < e ∧ 0 < f ∧ 0 < g ∧ 0 < h ∧ e ^ 2 + f ^ 2 = (p : ℤ) ∧ g ^ 2 + h ^ 2 = (q : ℤ)) ∧
      (0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D) ∧
      (A ^ 2 + B ^ 2 = (p : ℤ) * q ∧ C ^ 2 + D ^ 2 = (p : ℤ) * q) ∧
      (A ≠ B ∧ A ≠ C ∧ A ≠ D ∧ B ≠ C ∧ B ≠ D ∧ C ≠ D) := by
  obtain ⟨e, f, he, hf, hef', hef⟩ := exists_prime_rep hp hp4
  obtain ⟨g, h, hg, hh, hgh', hgh⟩ := exists_prime_rep hq hq4
  have hid1 : (e * g + f * h) ^ 2 + (e * h - f * g) ^ 2 = (p : ℤ) * q := by
    linear_combination (g ^ 2 + h ^ 2) * hef + (p : ℤ) * hgh
  have hid2 : (e * g - f * h) ^ 2 + (e * h + f * g) ^ 2 = (p : ℤ) * q := by
    linear_combination (g ^ 2 + h ^ 2) * hef + (p : ℤ) * hgh
  have hu : e * h - f * g ≠ 0 := by
    intro hz
    rw [hz] at hid1
    exact prime_mul_prime_ne_sq hp hq hpq (A := e * g + f * h) (by linarith)
  have hv : e * g - f * h ≠ 0 := by
    intro hz
    rw [hz] at hid2
    exact prime_mul_prime_ne_sq hp hq hpq (A := e * h + f * g) (by linarith)
  have hAB : (e * g + f * h) ^ 2 + |e * h - f * g| ^ 2 = (p : ℤ) * q := by rw [sq_abs]; exact hid1
  have hCD : |e * g - f * h| ^ 2 + (e * h + f * g) ^ 2 = (p : ℤ) * q := by rw [sq_abs]; exact hid2
  have hApos : (0:ℤ) < e * g + f * h := by positivity
  have hDpos : (0:ℤ) < e * h + f * g := by positivity
  have hBpos : (0:ℤ) < |e * h - f * g| := abs_pos.2 hu
  have hCpos : (0:ℤ) < |e * g - f * h| := abs_pos.2 hv
  -- `p*q` is odd, so a representation never has two equal parts
  have hodd : ∀ X : ℤ, X ^ 2 + X ^ 2 ≠ (p : ℤ) * q := by
    intro X hX
    have h2 : (2 : ℤ) ∣ ((p * q : ℕ) : ℤ) := ⟨X ^ 2, by push_cast; linarith⟩
    have h2' : 2 ∣ p * q := by exact_mod_cast h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2' with hd | hd
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 hd; omega
    · have := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hq).1 hd; omega
  have hACne : e * g + f * h ≠ |e * g - f * h| := by
    have : |e * g - f * h| < e * g + f * h := by
      rw [abs_lt]; constructor <;> nlinarith
    linarith
  have hBDne : |e * h - f * g| ≠ e * h + f * g := by
    have : |e * h - f * g| < e * h + f * g := by
      rw [abs_lt]; constructor <;> nlinarith
    linarith
  have hADne : e * g + f * h ≠ e * h + f * g := by
    intro hEq
    have hz : (e - f) * (g - h) = 0 := by linear_combination hEq
    rcases mul_eq_zero.1 hz with hz' | hz'
    · exact hef' (by linarith)
    · exact hgh' (by linarith)
  refine ⟨e, f, g, h, e * g + f * h, |e * h - f * g|, |e * g - f * h|, e * h + f * g,
    ⟨he, hf, hg, hh, hef, hgh⟩, ⟨hApos, hBpos, hCpos, hDpos⟩, ⟨hAB, hCD⟩,
    ?_, hACne, hADne, ?_, hBDne, ?_⟩
  · -- `A ≠ B`
    intro hEq
    exact hodd |e * h - f * g| (by rw [hEq] at hAB; exact hAB)
  · -- `B ≠ C`
    intro hEq
    have hAD : (e * g + f * h) ^ 2 = (e * h + f * g) ^ 2 := by rw [hEq] at hAB; linarith [hCD]
    exact hADne (by nlinarith [hApos, hDpos])
  · -- `C ≠ D`
    intro hEq
    exact hodd (e * h + f * g) (by rw [hEq] at hCD; exact hCD)

/-! ## Exactly two representations -/

/-- **Exactly two essentially distinct representations.**  For distinct primes
`p ≡ q ≡ 1 [MOD 4]`, the number `p*q` has exactly two representations as a sum of two positive
squares up to order: there are `A,B,C,D` with `A²+B² = C²+D² = p*q`, essentially distinct, and
*every* representation of `p*q` by two positive squares is `(A,B)`, `(B,A)`, `(C,D)` or
`(D,C)`. -/
theorem exactly_two_reps (hp : p.Prime) (hq : q.Prime) (hp4 : p % 4 = 1) (hq4 : q % 4 = 1)
    (hpq : p ≠ q) :
    ∃ A B C D : ℤ, 0 < A ∧ 0 < B ∧ 0 < C ∧ 0 < D ∧
      A ^ 2 + B ^ 2 = (p : ℤ) * q ∧ C ^ 2 + D ^ 2 = (p : ℤ) * q ∧
      ¬(C = A ∧ D = B) ∧ ¬(D = A ∧ C = B) ∧
      ∀ a b : ℤ, 0 < a → 0 < b → a ^ 2 + b ^ 2 = (p : ℤ) * q →
        (a = A ∧ b = B) ∨ (a = B ∧ b = A) ∨ (a = C ∧ b = D) ∨ (a = D ∧ b = C) := by
  obtain ⟨e, f, g, h, A, B, C, D, ⟨he, hf, hg, hh, hef, hgh⟩, ⟨hA, hB, hC, hD⟩, ⟨hAB, hCD⟩,
    hAneB, hAneC, hAneD, hBneC, hBneD, hCneD⟩ := exists_four_reps hp hq hp4 hq4 hpq
  have hBA : B ^ 2 + A ^ 2 = (p : ℤ) * q := by linarith
  have hDC : D ^ 2 + C ^ 2 = (p : ℤ) * q := by linarith
  refine ⟨A, B, C, D, hA, hB, hC, hD, hAB, hCD, fun hx => hAneC hx.1.symm,
    fun hx => hAneD hx.1.symm, ?_⟩
  intro a b ha hb hab
  by_contra hcon
  have key : ∀ x₁ y₁ x₂ y₂ : ℤ, 0 < x₁ → 0 < y₁ → 0 < x₂ → 0 < y₂ →
      x₁ ^ 2 + y₁ ^ 2 = (p : ℤ) * q → x₂ ^ 2 + y₂ ^ 2 = (p : ℤ) * q → ¬(x₂ = x₁ ∧ y₂ = y₁) →
      ((decide ((p : ℤ) ∣ (x₁ * f - y₁ * e)), decide ((q : ℤ) ∣ (x₁ * h - y₁ * g))) :
          Bool × Bool) ≠
        (decide ((p : ℤ) ∣ (x₂ * f - y₂ * e)), decide ((q : ℤ) ∣ (x₂ * h - y₂ * g))) := by
    intro x₁ y₁ x₂ y₂ h1 h2 h3 h4 hr1 hr2 hne hEq
    exact hne (rep_eq_of_same_classes hp hq hpq he hf hg hh hef hgh h1 h2 h3 h4 hr1 hr2
      (decide_eq_decide.1 (congrArg Prod.fst hEq)) (decide_eq_decide.1 (congrArg Prod.snd hEq)))
  exact pigeonhole_four_classes _ _ _ _ _
    (key a b A B ha hb hA hB hab hAB (fun hx => hcon (Or.inl ⟨hx.1.symm, hx.2.symm⟩)))
    (key a b B A ha hb hB hA hab hBA (fun hx => hcon (Or.inr (Or.inl ⟨hx.1.symm, hx.2.symm⟩))))
    (key a b C D ha hb hC hD hab hCD
      (fun hx => hcon (Or.inr (Or.inr (Or.inl ⟨hx.1.symm, hx.2.symm⟩)))))
    (key a b D C ha hb hD hC hab hDC
      (fun hx => hcon (Or.inr (Or.inr (Or.inr ⟨hx.1.symm, hx.2.symm⟩)))))
    (key A B B A hA hB hB hA hAB hBA (fun hx => hAneB hx.1.symm))
    (key A B C D hA hB hC hD hAB hCD (fun hx => hAneC hx.1.symm))
    (key A B D C hA hB hD hC hAB hDC (fun hx => hAneD hx.1.symm))
    (key B A C D hB hA hC hD hBA hCD (fun hx => hBneC hx.1.symm))
    (key B A D C hB hA hD hC hBA hDC (fun hx => hBneD hx.1.symm))
    (key C D D C hC hD hD hC hCD hDC (fun hx => hCneD hx.1.symm))

/-! ## The empty cells: a prime `3 mod 4` to an odd power -/

/-- If a prime `r ≡ 3 [MOD 4]` divides `n` exactly once, then `n` is not a sum of two squares. -/
theorem no_rep_of_three_mod_four {r n : ℕ} (hr : r.Prime) (hr4 : r % 4 = 3) (hdvd : r ∣ n)
    (hsq : ¬ (r ^ 2 ∣ n)) (a b : ℤ) : a ^ 2 + b ^ 2 ≠ (n : ℤ) := by
  intro hab
  haveI := Fact.mk hr
  have hrn : (r : ℤ) ∣ (a ^ 2 + b ^ 2) := by
    rw [hab]; exact_mod_cast Int.natCast_dvd_natCast.2 hdvd
  have h0 : ((a : ZMod r)) ^ 2 + ((b : ZMod r)) ^ 2 = 0 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a ^ 2 + b ^ 2) r).2 hrn
    push_cast at this
    exact this
  have ha0 : ((a : ZMod r)) = 0 := by
    by_contra hne
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq (y := (b : ZMod r)) hne
      (by linear_combination h0) hr4
  have hb0 : ((b : ZMod r)) = 0 := by
    by_contra hne
    exact ZMod.mod_four_ne_three_of_sq_eq_neg_sq' (x := (a : ZMod r)) hne
      (by linear_combination h0) hr4
  have hra : (r : ℤ) ∣ a := (ZMod.intCast_zmod_eq_zero_iff_dvd a r).1 ha0
  have hrb : (r : ℤ) ∣ b := (ZMod.intCast_zmod_eq_zero_iff_dvd b r).1 hb0
  obtain ⟨a', rfl⟩ := hra
  obtain ⟨b', rfl⟩ := hrb
  have : ((r : ℤ)) ^ 2 ∣ (n : ℤ) := ⟨a' ^ 2 + b' ^ 2, by linear_combination -hab⟩
  exact hsq (by exact_mod_cast this)

/-- **The dichotomy of the semiprime table.**  For distinct odd primes `p ≠ q`, the number
`p*q` admits two essentially distinct two-square representations (the input Euler's method
needs) if and only if both primes are `1 mod 4`.  In every other class the eligible set is
empty. -/
theorem euler_works_iff_both_one_mod_four (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) (hpq : p ≠ q) :
    (∃ a b c d : ℤ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a ^ 2 + b ^ 2 = (p : ℤ) * q ∧
        c ^ 2 + d ^ 2 = (p : ℤ) * q ∧ ¬(c = a ∧ d = b) ∧ ¬(d = a ∧ c = b)) ↔
      (p % 4 = 1 ∧ q % 4 = 1) := by
  have hpodd : p % 4 = 1 ∨ p % 4 = 3 := by
    have : p % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · exact absurd h hp2
      · exact h
    omega
  have hqodd : q % 4 = 1 ∨ q % 4 = 3 := by
    have : q % 2 = 1 := by
      rcases hq.eq_two_or_odd with h | h
      · exact absurd h hq2
      · exact h
    omega
  constructor
  · rintro ⟨a, b, c, d, ha, hb, hc, hd, hab, hcd, hne1, hne2⟩
    have hcast : a ^ 2 + b ^ 2 = ((p * q : ℕ) : ℤ) := by push_cast; exact hab
    constructor
    · rcases hpodd with h | h
      · exact h
      · exfalso
        refine no_rep_of_three_mod_four hp h (Dvd.intro q rfl) ?_ a b hcast
        intro hdvd
        have : p ∣ q := by
          have h2 : p * p ∣ p * q := by
            rcases hdvd with ⟨k, hk⟩; exact ⟨k, by rw [hk]; ring⟩
          exact (mul_dvd_mul_iff_left hp.pos.ne').1 h2
        exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 this)
    · rcases hqodd with h | h
      · exact h
      · exfalso
        refine no_rep_of_three_mod_four hq h (Dvd.intro_left p rfl) ?_ a b hcast
        intro hdvd
        have : q ∣ p := by
          have h2 : q * q ∣ q * p := by
            rcases hdvd with ⟨k, hk⟩; exact ⟨k, by rw [mul_comm q p, hk]; ring⟩
          exact (mul_dvd_mul_iff_left hq.pos.ne').1 h2
        exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 this).symm
  · rintro ⟨hp4, hq4⟩
    obtain ⟨A, B, C, D, hA, hB, hC, hD, hAB, hCD, h1, h2, -⟩ :=
      exactly_two_reps hp hq hp4 hq4 hpq
    exact ⟨A, B, C, D, hA, hB, hC, hD, hAB, hCD, h1, h2⟩

end EulerTwoSquares
-- ==== upstream: Packages/Catalog/Algebra/EulerTwoSquaresRepCount.lean ====
/-!
# The representation count, as a finite cardinality

`EulerTwoSquares.exactly_two_reps` describes the representations of `p*q` as a list of four
ordered integer pairs.  Here we package the same information as a *cardinality*: the finite
set of normalised representations

`repFinset n = {(a,b) : 0 < a ≤ b, a² + b² = n}`

has exactly two elements when `n = p*q` for distinct primes `p ≡ q ≡ 1 [MOD 4]`.  This is the
form in which the eligibility statistics of a factorisation experiment are actually measured.
-/

namespace EulerTwoSquares

variable {p q : ℕ}

-- [dropped: platform already declares repFinset]
theorem mem_repFinset {n : ℕ} {z : ℕ × ℕ} :
    z ∈ repFinset n ↔ 0 < z.1 ∧ z.1 ≤ z.2 ∧ z.1 ^ 2 + z.2 ^ 2 = n := by
  simp only [repFinset, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  constructor
  · rintro ⟨-, h⟩; exact h
  · rintro ⟨h1, h2, h3⟩
    have hz1 : z.1 ≤ z.1 ^ 2 := Nat.le_self_pow (by norm_num) _
    have hz2 : z.2 ≤ z.2 ^ 2 := Nat.le_self_pow (by norm_num) _
    exact ⟨⟨by omega, by omega⟩, h1, h2, h3⟩

/-- A positive integral representation, normalised, is an element of `repFinset`. -/
theorem minmax_mem_repFinset {n : ℕ} {U V : ℤ} (hU : 0 < U) (hV : 0 < V)
    (h : U ^ 2 + V ^ 2 = (n : ℤ)) : ((min U V).toNat, (max U V).toNat) ∈ repFinset n := by
  have hmin : 0 < min U V := lt_min hU hV
  have hmax : min U V ≤ max U V := min_le_max
  have hsum : (min U V) ^ 2 + (max U V) ^ 2 = (n : ℤ) := by
    rcases le_total U V with hle | hle
    · rw [min_eq_left hle, max_eq_right hle]; exact h
    · rw [min_eq_right hle, max_eq_left hle]; linarith [h]
  refine mem_repFinset.2 ⟨?_, ?_, ?_⟩
  · simpa using hmin
  · exact Int.toNat_le_toNat hmax
  · have hc : (((min U V).toNat : ℤ)) ^ 2 + (((max U V).toNat : ℤ)) ^ 2 = (n : ℤ) := by
      rw [Int.toNat_of_nonneg hmin.le, Int.toNat_of_nonneg (hmin.le.trans hmax)]
      exact hsum
    exact_mod_cast hc

/-- Reading a normalised pair back as the `min`/`max` of an integral representation. -/
theorem pair_eq_minmax {U V : ℤ} {z : ℕ × ℕ} (h1 : (z.1 : ℤ) = U) (h2 : (z.2 : ℤ) = V)
    (hle : z.1 ≤ z.2) : z = ((min U V).toNat, (max U V).toNat) := by
  have hUV : U ≤ V := by rw [← h1, ← h2]; exact_mod_cast hle
  rw [min_eq_left hUV, max_eq_right hUV, ← h1, ← h2]
  simp

theorem pair_eq_minmax' {U V : ℤ} {z : ℕ × ℕ} (h1 : (z.1 : ℤ) = V) (h2 : (z.2 : ℤ) = U)
    (hle : z.1 ≤ z.2) : z = ((min U V).toNat, (max U V).toNat) := by
  have hUV : V ≤ U := by rw [← h1, ← h2]; exact_mod_cast hle
  rw [min_eq_right hUV, max_eq_left hUV, ← h1, ← h2]
  simp

/-- **The representation count of an eligible semiprime is exactly two.**  For distinct primes
`p ≡ q ≡ 1 [MOD 4]` the finite set of normalised two-square representations of `p*q` has
cardinality `2`. -/
theorem repFinset_card_eq_two (hp : p.Prime) (hq : q.Prime) (hp4 : p % 4 = 1) (hq4 : q % 4 = 1)
    (hpq : p ≠ q) : (repFinset (p * q)).card = 2 := by
  obtain ⟨A, B, C, D, hA, hB, hC, hD, hAB, hCD, hne1, hne2, hall⟩ :=
    exactly_two_reps hp hq hp4 hq4 hpq
  have hABn : A ^ 2 + B ^ 2 = ((p * q : ℕ) : ℤ) := by push_cast; exact hAB
  have hCDn : C ^ 2 + D ^ 2 = ((p * q : ℕ) : ℤ) := by push_cast; exact hCD
  set x : ℕ × ℕ := ((min A B).toNat, (max A B).toNat) with hxdef
  set y : ℕ × ℕ := ((min C D).toNat, (max C D).toNat) with hydef
  have hxmem : x ∈ repFinset (p * q) := minmax_mem_repFinset hA hB hABn
  have hymem : y ∈ repFinset (p * q) := minmax_mem_repFinset hC hD hCDn
  have hxy : x ≠ y := by
    intro hEq
    have hmin : min A B = min C D := by
      have := congrArg Prod.fst hEq
      simp only [hxdef, hydef] at this
      have h1 : (0 : ℤ) ≤ min A B := (lt_min hA hB).le
      have h2 : (0 : ℤ) ≤ min C D := (lt_min hC hD).le
      omega
    have hmax : max A B = max C D := by
      have := congrArg Prod.snd hEq
      simp only [hxdef, hydef] at this
      have h1 : (0 : ℤ) ≤ max A B := le_trans hA.le (le_max_left _ _)
      have h2 : (0 : ℤ) ≤ max C D := le_trans hC.le (le_max_left _ _)
      omega
    rcases le_total A B with hab | hab <;> rcases le_total C D with hcd | hcd
    · rw [min_eq_left hab, min_eq_left hcd] at hmin
      rw [max_eq_right hab, max_eq_right hcd] at hmax
      exact hne1 ⟨hmin.symm, hmax.symm⟩
    · rw [min_eq_left hab, min_eq_right hcd] at hmin
      rw [max_eq_right hab, max_eq_left hcd] at hmax
      exact hne2 ⟨hmin.symm, hmax.symm⟩
    · rw [min_eq_right hab, min_eq_left hcd] at hmin
      rw [max_eq_left hab, max_eq_right hcd] at hmax
      exact hne2 ⟨hmax.symm, hmin.symm⟩
    · rw [min_eq_right hab, min_eq_right hcd] at hmin
      rw [max_eq_left hab, max_eq_left hcd] at hmax
      exact hne1 ⟨hmax.symm, hmin.symm⟩
  have hset : repFinset (p * q) = {x, y} := by
    apply Finset.ext
    intro z
    constructor
    · intro hz
      obtain ⟨hz1, hz2, hz3⟩ := mem_repFinset.1 hz
      have hz1' : (0 : ℤ) < (z.1 : ℤ) := by exact_mod_cast hz1
      have hz2' : (0 : ℤ) < (z.2 : ℤ) := by omega
      have hz3' : (z.1 : ℤ) ^ 2 + (z.2 : ℤ) ^ 2 = (p : ℤ) * q := by
        have : ((z.1 ^ 2 + z.2 ^ 2 : ℕ) : ℤ) = ((p * q : ℕ) : ℤ) := by exact_mod_cast hz3
        push_cast at this
        exact this
      rcases hall (z.1 : ℤ) (z.2 : ℤ) hz1' hz2' hz3' with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
      · exact Finset.mem_insert.2 (Or.inl (pair_eq_minmax e1 e2 hz2))
      · exact Finset.mem_insert.2 (Or.inl (pair_eq_minmax' e1 e2 hz2))
      · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2
          (pair_eq_minmax e1 e2 hz2)))
      · exact Finset.mem_insert.2 (Or.inr (Finset.mem_singleton.2
          (pair_eq_minmax' e1 e2 hz2)))
    · intro hz
      rcases Finset.mem_insert.1 hz with h | h
      · rw [h]; exact hxmem
      · rw [Finset.mem_singleton.1 h]; exact hymem
  rw [hset, Finset.card_pair hxy]

end EulerTwoSquares
section
open EulerTwoSquares
variable {p q : ℕ}

theorem solution (hp : p.Prime) (hq : q.Prime) (hp4 : p % 4 = 1) (hq4 : q % 4 = 1)
    (hpq : p ≠ q) :
    (repFinset (p * q)).card = 2 :=
  EulerTwoSquares.repFinset_card_eq_two hp hq hp4 hq4 hpq

end
