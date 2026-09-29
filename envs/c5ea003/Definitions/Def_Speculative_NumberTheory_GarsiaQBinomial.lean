-- Prove2me | Definitions.Def_Speculative_NumberTheory_GarsiaQBinomial
-- name    : Speculative_NumberTheory_GarsiaQBinomial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:33:49.645232+00:00
-- url     : https://prove2.me/theorems/0e726312-a3ca-48fb-8d8a-913a8bfe0320
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_GarsiaQBinomial
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.GarsiaQBinomial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/GarsiaQBinomial.lean by skeleton subtraction
import Mathlib

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

namespace GarsiaQBinom

open Polynomial

open scoped BigOperators

/-- The q-integer `[n]_q = 1 + q + q² + ⋯ + q^{n-1}` as an element of `ℤ[q]`. -/
noncomputable def qNat (n : ℕ) : Polynomial ℤ := ∑ i ∈ Finset.range n, X ^ i

/-- The Gaussian binomial coefficient `⟦ n choose k ⟧_q ∈ ℤ[q]`, defined via the
q-Pascal recurrence. -/
noncomputable def qBinom : ℕ → ℕ → Polynomial ℤ
  | _, 0 => 1
  | 0, (_ + 1) => 0
  | (n + 1), (k + 1) => qBinom n k + X ^ (k + 1) * qBinom n (k + 1)
















/-- The q-factorial `[n]_q! = [1]_q · [2]_q ⋯ [n]_q ∈ ℤ[q]`. -/
noncomputable def qFactorial : ℕ → Polynomial ℤ
  | 0 => 1
  | (n + 1) => qFactorial n * qNat (n + 1)






end GarsiaQBinom


