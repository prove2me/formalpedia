-- Prove2me | Definitions.Def_Probability_BinaryTwoBinomial
-- name    : Probability_BinaryTwoBinomial
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:42.084982+00:00
-- url     : https://prove2.me/theorems/b40f2348-338a-4f5f-b730-18e427fc95ce
-- title:
--   Aether Catalog definitions — Probability_BinaryTwoBinomial
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.BinaryTwoBinomial`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/BinaryTwoBinomial.lean by skeleton subtraction
import Mathlib

/-!
# Central Gaussian coefficient maximizes binary 2-binomial class size

This file develops the combinatorics of the **2-binomial equivalence classes** of binary
words and connects their sizes to the **Gaussian (q-)binomial coefficients**.

## Background

Two finite binary words `u, v` are *2-binomially equivalent* (Rigo–Salimov) when they
contain the same number of scattered occurrences of every factor of length `≤ 2`.
For binary words this is equivalent to: same length `n`, same number of ones `k`, and the
same *inversion number* `inv` (number of pairs `(i, j)` with `i < j`, position `i` a one and
position `j` a zero — i.e. scattered occurrences of the factor `10`).

Hence a 2-binomial class is indexed by the triple `(n, k, i)` and its cardinality, the
`classSize n k i`, is exactly the coefficient of `q^i` in the Gaussian binomial coefficient
`[n choose k]_q` (MacMahon's theorem). The Gaussian binomial coefficients are symmetric and
unimodal, so the *central* coefficient is the maximum: the central inversion number gives the
largest 2-binomial class.

We model a binary word of length `n` with `k` ones by the set `S : Finset (Fin n)` of
positions carrying a one (`|S| = k`).

## Main results

* `invF_le`            : the inversion number is at most `k * (n - k)`.
* `classSize_eq_zero_of_gt` : classes vanish past the maximal inversion number.
* `total_eq_choose`    : the class sizes sum to `n.choose k` (rows sum to a binomial).
* `classSize_symm`     : palindromic symmetry `classSize n k i = classSize n k (k*(n-k) - i)`.
* `central_max_*`      : for explicit `(n, k)`, the central coefficient is the global maximum.

-- !-- Lab Notes -- !--
Hypothesis log / experimental record.

H1. classSize n k i = coeff of q^i in [n choose k]_q.
    EVIDENCE: #eval of classSize for (4,2),(5,2),(6,3) reproduced exactly the known
    Gaussian rows 1,1,2,1,1 / 1,1,2,2,2,1,1 / 1,1,2,3,3,3,3,2,1,1.  CONFIRMED.

H2. The class sizes for fixed (n,k) sum to C(n,k).
    EVIDENCE: ∑_i classSize 5 2 i = 10 = C(5,2).  CONFIRMED → `total_eq_choose`.

H3. The distribution is palindromic about k(n-k)/2.
    EVIDENCE: rows above are all palindromes.  CONFIRMED → `classSize_symm`
    (bijection: reverse the word, which swaps inversions `10` with co-inversions `01`).

H4 (headline). The maximum class size is attained at the central inversion number
    c = k(n-k)/2.  This is full unimodality of Gaussian binomials — a deep theorem
    (Sylvester via hard Lefschetz; first elementary proof O'Hara 1990).  We do NOT prove
    the general statement here (left as a FUTURE_DIRECTIONS conjecture); instead we verify
    it as fully-checked theorems for explicit (n,k) via kernel/native computation.

FAILURE ANALYSIS: an early attempt represented words as `Fin n → Bool`; counting the total
as C(n,k) was awkward.  Switching to `Finset (Fin n)` (the positions of the ones) makes the
total immediate from `Finset.card_powersetCard`.
-/

namespace BinaryTwoBinomial

open Finset

/-- The inversion number of a binary word whose ones sit at positions `S ⊆ Fin n`:
the number of ordered pairs `(i, j)` with `i < j`, position `i` a one and position `j` a
zero (scattered occurrences of the factor `10`). -/
def invF {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  (univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S)).card

/-- The co-inversion number: pairs `(i, j)`, `i < j`, with `i` a zero and `j` a one
(scattered occurrences of `01`). -/
def coinvF {n : ℕ} (S : Finset (Fin n)) : ℕ :=
  (univ.filter (fun p : Fin n × Fin n => p.1 < p.2 ∧ p.1 ∉ S ∧ p.2 ∈ S)).card

/-- The set of binary words of length `n` with exactly `k` ones (positions of the ones). -/
def words (n k : ℕ) : Finset (Finset (Fin n)) := (univ : Finset (Fin n)).powersetCard k

/-- The size of the 2-binomial class `(n, k, i)`: binary words of length `n` with `k` ones
and inversion number `i`. Equivalently, the coefficient of `q^i` in `[n choose k]_q`. -/
def classSize (n k i : ℕ) : ℕ := ((words n k).filter (fun S => invF S = i)).card

/-- The central inversion number `k(n-k)/2`. -/
def centralIndex (n k : ℕ) : ℕ := k * (n - k) / 2


/-
The inversion number of a word with `k` ones is at most `k * (n - k)`.
-/

/-
Beyond the maximal inversion number the class is empty.
-/

/-
The 2-binomial class sizes for fixed `(n, k)` sum to the binomial coefficient `C(n,k)`.
-/

/-
Reversing a word swaps inversions and co-inversions.
-/

/-
Inversions and co-inversions of a `k`-one word partition the `k(n-k)` mixed pairs.
-/

/-
**Palindromic symmetry** of the 2-binomial class sizes: the class at inversion number
`i` has the same size as the class at the mirror inversion number `k(n-k) - i`.
-/

/-
**Expected inversion number is central.** Drawing a binary word of length `n` with `k`
ones uniformly at random, the mean inversion number is `k(n-k)/2` — the central index. In
cleared (denominator-free) form: `2 * Σ i·classSize = k(n-k) · C(n,k)`. This is a direct
consequence of the palindromic symmetry `classSize_symm`.
-/

-- !-- Lab Notes -- !--
-- Headline experiments: central coefficient is the *global* maximum for explicit (n,k).
-- Each is a genuine theorem quantified over all i : ℕ (the tail i > k(n-k) is handled by
-- `classSize_eq_zero_of_gt`, the support is checked by computation).





end BinaryTwoBinomial


