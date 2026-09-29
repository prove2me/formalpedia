-- Prove2me | solution 1 for EulerTwoSquares.exists_four_reps
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T19:32:43.898266+00:00
-- url     : https://prove2.me/submissions/82d6f655-eeb5-4d06-91b3-978a6bba9346

-- Sol generated from Algebra/EulerTwoSquaresCount.lean
import Mathlib
import Theorems.Thm_EulerTwoSquares_prime_mul_prime_ne_sq

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

open EulerTwoSquares


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


/-! ## The class bits attached to a representation -/

variable {p q : ℕ}





/-! ## The Brahmagupta construction: four ordered representations -/



/-! ## Exactly two representations -/


/-! ## The empty cells: a prime `3 mod 4` to an odd power -/




open EulerTwoSquares in
theorem solution(hp : p.Prime) (hq : q.Prime) (hp4 : p % 4 = 1) (hq4 : q % 4 = 1)
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
