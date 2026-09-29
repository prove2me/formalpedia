-- Prove2me | solution 1 for GarsiaQBinom.qBinom_pascal_p
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-18T20:28:21.895333+00:00
-- url     : https://prove2.me/submissions/dcc78a1a-48c3-4c85-aaeb-2a86ce7b2bc3

-- Sol generated from Speculative/NumberTheory/GarsiaQBinomial.lean
import Mathlib
import Definitions.Def_Speculative_NumberTheory_GarsiaQBinomial

/-!
# Gaussian binomial coefficients (q-binomials)

A memorial-tribute companion file for *Adriano Garsia (1928–2024)*.  Garsia's
mathematical life was devoted to **q-analogs** and their combinatorics: the
theory of Macdonald polynomials, the `(q,t)`-Catalan numbers, the
Garsia–Haiman modules, and the shuffle theory of the diagonal harmonics.  At the
heart of every one of these subjects sit the **Gaussian binomial coefficients**
`⟦ n choose k ⟧_q`, the q-analog of the ordinary binomial coefficients.

This file develops a small, self-contained theory of these polynomials over
`ℤ[q]` (here `q = Polynomial.X`), defined through the **q-Pascal recurrence**

  `⟦ n+1 , k+1 ⟧ = ⟦ n , k ⟧ + q^(k+1) · ⟦ n , k+1 ⟧`.

We prove:

* `qBinom_eq_zero_of_lt`     : the coefficient vanishes for `k > n`;
* `qBinom_self`              : `⟦ n , n ⟧ = 1`;
* `qBinom_one_right`         : `⟦ n , 1 ⟧ = [n]_q = 1 + q + ⋯ + q^{n-1}`;
* `qBinom_pascal'`           : the *dual* q-Pascal recurrence
                               `⟦ n+1 , k+1 ⟧ = q^{n-k}·⟦ n , k ⟧ + ⟦ n , k+1 ⟧`;
* `qBinom_symm`              : the symmetry `⟦ n , k ⟧ = ⟦ n , n-k ⟧`;
* `qBinom_eval_one`          : the specialization `q = 1` recovers the ordinary
                               binomial coefficient `Nat.choose n k`;
* `qNat_eval_one`            : `[n]_q` specializes to `n` at `q = 1`;
* `qNat_add`                 : additivity of q-integers `[a+b]_q = [a]_q + q^a·[b]_q`;
* `qFactorial_product`       : the **q-factorial product formula**
                               `⟦n,k⟧_q · [k]_q! · [n-k]_q! = [n]_q!`, the
                               division-free q-analog of `C(n,k)·k!·(n-k)! = n!`;
* `qFactorial_eval_one`      : `[n]_q!` specializes to `n!` at `q = 1`;
* `choose_mul_factorial_from_q` : the classical `C(n,k)·k!·(n-k)! = n!` as a
                               `q = 1` corollary of the product formula.

All results are proved from scratch; nothing here relies on a pre-existing
Gaussian-binomial theory.
-/

open GarsiaQBinom

open Polynomial

open scoped BigOperators



@[simp] theorem qBinom_zero_right (n : ℕ) : qBinom n 0 = 1 := by
  cases n <;> rfl


theorem qBinom_succ_succ (n k : ℕ) :
    qBinom (n + 1) (k + 1) = qBinom n k + X ^ (k + 1) * qBinom n (k + 1) := rfl

/-- The Gaussian binomial coefficient vanishes when `k > n`. -/
theorem qBinom_eq_zero_of_lt {n k : ℕ} (h : n < k) : qBinom n k = 0 := by
  induction n generalizing k with
  | zero => cases k with
    | zero => omega
    | succ k => rfl
  | succ n ih => cases k with
    | zero => omega
    | succ k => rw [qBinom_succ_succ, ih (by omega), ih (by omega), mul_zero, add_zero]

/-- `⟦ n , n ⟧_q = 1`. -/
@[simp] theorem qBinom_self (n : ℕ) : qBinom n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [qBinom_succ_succ, ih, qBinom_eq_zero_of_lt (Nat.lt_succ_self n), mul_zero, add_zero]

/-- The `q`-integer recurrence `[n+1]_q = 1 + q·[n]_q`. -/
theorem qNat_succ (n : ℕ) : qNat (n + 1) = 1 + X * qNat n := by
  rw [qNat, qNat, geom_sum_succ]
  ring

/-- The `q`-integer recurrence `[n+1]_q = [n]_q + q^n`. -/
theorem qNat_succ' (n : ℕ) : qNat (n + 1) = qNat n + X ^ n := by
  rw [qNat, qNat, Finset.sum_range_succ]

/-- `⟦ n , 1 ⟧_q = [n]_q`. -/
theorem qBinom_one_right (n : ℕ) : qBinom n 1 = qNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [show (1 : ℕ) = 0 + 1 from rfl, qBinom_succ_succ, qBinom_zero_right, ih,
      qNat_succ]
    ring















open GarsiaQBinom in
theorem solution: ∀ {n k : ℕ}, k ≤ n →
    qBinom (n + 1) (k + 1) = X ^ (n - k) * qBinom n k + qBinom n (k + 1) := by
  intro n
  induction n with
  | zero =>
    intro k hk
    interval_cases k
    simp [qBinom]
  | succ n ih =>
    intro k hk
    cases k with
    | zero =>
      have hL : qBinom (n + 1 + 1) (0 + 1) = 1 + X * qNat (n + 1) := by
        rw [qBinom_succ_succ, qBinom_zero_right, qBinom_one_right, pow_one]
      have hR : X ^ (n + 1 - 0) * qBinom (n + 1) 0 + qBinom (n + 1) (0 + 1)
              = X ^ (n + 1) + qNat (n + 1) := by
        rw [qBinom_zero_right, mul_one, qBinom_one_right, Nat.sub_zero]
      rw [hL, hR, ← qNat_succ (n + 1), qNat_succ' (n + 1)]
      ring
    | succ m =>
      have hm : m ≤ n := Nat.succ_le_succ_iff.mp hk
      rcases lt_or_eq_of_le hm with hlt | heq
      · -- `m < n`: expand both sides down to level `n`
        have e1 : (X : Polynomial ℤ) ^ (m + 1 + 1) * X ^ (n - (m + 1)) = X ^ (n + 1) := by
          rw [← pow_add]; congr 1; omega
        have e2 : (X : Polynomial ℤ) ^ (n - m) * X ^ (m + 1) = X ^ (n + 1) := by
          rw [← pow_add]; congr 1; omega
        have hL : qBinom (n + 1 + 1) (m + 1 + 1)
            = X ^ (n - m) * qBinom n m + qBinom n (m + 1)
              + X ^ (n + 1) * qBinom n (m + 1) + X ^ (m + 1 + 1) * qBinom n (m + 1 + 1) := by
          rw [qBinom_succ_succ (n + 1) (m + 1), ih hm, ih hlt]
          rw [mul_add, ← mul_assoc, e1]
          ring
        have hR : X ^ (n + 1 - (m + 1)) * qBinom (n + 1) (m + 1) + qBinom (n + 1) (m + 1 + 1)
            = X ^ (n - m) * qBinom n m + X ^ (n + 1) * qBinom n (m + 1)
              + qBinom n (m + 1) + X ^ (m + 1 + 1) * qBinom n (m + 1 + 1) := by
          have e0 : n + 1 - (m + 1) = n - m := by omega
          rw [e0, qBinom_succ_succ n m, qBinom_succ_succ n (m + 1)]
          rw [mul_add, ← mul_assoc, e2]
          ring
        rw [hL, hR]; ring
      · -- `m = n`: both sides collapse to `1`
        subst heq
        rw [qBinom_succ_succ (m + 1) (m + 1), qBinom_self,
            qBinom_eq_zero_of_lt (by omega : m + 1 < m + 1 + 1)]
        simp
