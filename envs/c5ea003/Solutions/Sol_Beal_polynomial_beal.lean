-- Prove2me | solution 1 for Beal.polynomial_beal
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-10T22:53:16.770664+00:00
-- url     : https://prove2.me/submissions/d68033b9-6d78-49d9-a229-f183c5c46349

-- Sol generated from NumberTheory/BealPolynomial.lean
import Mathlib
import Definitions.Def_NumberTheory_BealPolynomial

/-!
# The function-field analogue of Beal's conjecture is a theorem

Over the integers Beal's conjecture is open.  Over a polynomial ring `k[X]` with `k` a field of
characteristic zero the analogous statement is *provable*, via the Mason–Stothers theorem (the
polynomial `abc` theorem), which is available in Mathlib as `Polynomial.flt_catalan`.

The main results are:

* `Beal.polynomial_beal`: if `a ^ x + b ^ y = c ^ z` in `k[X]` with `x, y, z ≥ 3`, all three
  polynomials nonzero, and at least one of them non-constant, then `a, b, c` have a common
  prime (irreducible) factor — the exact analogue of Beal's conjecture.
* `Beal.polynomial_beal_coprime`: equivalently, a coprime solution has only constant entries.
* `Beal.PolynomialBealConjecture` / `Beal.polynomialBealConjecture_holds`: the statement packaged
  in the same shape as `Beal.BealConjecture`, and its proof.

Together with `Beal.abc_implies_beal_counterexamples_bounded`, this exhibits the same mechanism
(`abc`/Mason–Stothers plus the hyperbolicity inequality `1/x + 1/y + 1/z ≤ 1`) in the two
settings: over function fields the inequality is already enough, over `ℤ` one needs the
(conjectural) `abc` inequality with an error term.
-/

open Beal

open Polynomial

variable {k : Type*} [Field k] [CharZero k]

/-- The hyperbolicity inequality in the multiplicative form required by
`Polynomial.flt_catalan`: for `x, y, z ≥ 3` we have `yz + zx + xy ≤ xyz`
(equivalently `1/x + 1/y + 1/z ≤ 1`). -/
theorem hyperbolic_ineq {x y z : ℕ} (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z) :
    y * z + z * x + x * y ≤ x * y * z := by
  have h1 : 3 * (y * z) ≤ x * (y * z) := Nat.mul_le_mul_right _ hx
  have h2 : 3 * (z * x) ≤ y * (z * x) := Nat.mul_le_mul_right _ hy
  have h3 : 3 * (x * y) ≤ z * (x * y) := Nat.mul_le_mul_right _ hz
  linarith

omit [CharZero k] in
/-- A prime of `k[X]` dividing two of `a, b, c` divides the third. -/
theorem polynomial_dvd_third {a b c : k[X]} {x y z : ℕ} {p : k[X]} (hp : Prime p)
    (hx : 0 < x) (hy : 0 < y) (heq : a ^ x + b ^ y = c ^ z) (hpa : p ∣ a) (hpb : p ∣ b) :
    p ∣ c := by
  have hcz : p ∣ c ^ z := by
    rw [← heq]
    exact dvd_add (dvd_pow hpa hx.ne') (dvd_pow hpb hy.ne')
  exact hp.dvd_of_dvd_pow hcz








open Beal in
theorem solution{a b c : k[X]} {x y z : ℕ}
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hx : 3 ≤ x) (hy : 3 ≤ y) (hz : 3 ≤ z)
    (heq : a ^ x + b ^ y = c ^ z)
    (hnonconst : a.natDegree ≠ 0 ∨ b.natDegree ≠ 0 ∨ c.natDegree ≠ 0) :
    ∃ p : k[X], Prime p ∧ p ∣ a ∧ p ∣ b ∧ p ∣ c := by
  by_contra hno
  push_neg at hno
  -- without a common prime factor, `a` and `b` are coprime
  have hab : IsCoprime a b := by
    refine isCoprime_of_prime_dvd (by tauto) ?_
    intro p hp hpa hpb
    exact hno p hp hpa hpb
      (polynomial_dvd_third hp (by omega) (by omega) heq hpa hpb)
  -- Mason–Stothers (via `Polynomial.flt_catalan`) forces all three to be constant
  have heq' : C (1 : k) * a ^ x + C (1 : k) * b ^ y + C (-1 : k) * c ^ z = 0 := by
    simp only [map_one, map_neg, one_mul, neg_mul]
    rw [heq]
    ring
  have hcast : ∀ n : ℕ, 3 ≤ n → (n : k) ≠ 0 := by
    intro n hn
    exact_mod_cast Nat.cast_ne_zero.mpr (by omega : n ≠ 0)
  obtain ⟨hda, hdb, hdc⟩ :=
    Polynomial.flt_catalan (k := k) (p := x) (q := y) (r := z)
      (by omega) (by omega) (by omega) (hyperbolic_ineq hx hy hz)
      (hcast x hx) (hcast y hy) (hcast z hz) ha hb hc hab
      one_ne_zero one_ne_zero (by norm_num) heq'
  rcases hnonconst with h | h | h
  · exact h hda
  · exact h hdb
  · exact h hdc
