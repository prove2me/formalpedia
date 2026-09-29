-- Prove2me | Theorems.Thm_BinaryTwoBinomial_classSize_symm
-- name    : BinaryTwoBinomial.classSize_symm
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:59:54.569539+00:00
-- url     : https://prove2.me/theorems/0f9e6926-ba4f-4b54-840e-f1a88291743f
-- title:
--   ClassSize symm
-- statement:
--   Formal statement of `BinaryTwoBinomial.classSize_symm` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem BinaryTwoBinomial.classSize_symm(n k i : ℕ) (hi : i ≤ k * (n - k)) :
--       classSize n k i = classSize n k (k * (n - k) - i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/BinaryTwoBinomial.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/BinaryTwoBinomial.lean#L146

-- Thm stub generated from Probability/BinaryTwoBinomial.lean
import Mathlib
import Definitions.Def_Probability_BinaryTwoBinomial

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

open BinaryTwoBinomial

open Finset







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

theorem BinaryTwoBinomial.classSize_symm(n k i : ℕ) (hi : i ≤ k * (n - k)) :
    classSize n k i = classSize n k (k * (n - k) - i) := by sorry
