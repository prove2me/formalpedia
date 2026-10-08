-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter03
-- name    : ProofsInTheBook_Chapter03
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T16:16:45.046244+00:00
-- url     : https://prove2.me/theorems/05ebb0b8-a83a-4ab9-ac5c-59dd1e2d6347
-- title:
--   Prime-factor thresholds, prime-gap covers, and power-free parts
-- statement:
--   For natural numbers k,m, the predicate HasPrimeFactorAbove(k,m) means that some prime p>k divides m. NoLargePrimeFactor(k,m) means that every prime divisor of m is at most k. The auxiliary analytic expression is
--   $$H(n,k)=n\log n-k\log k-(n\mathbin{\dot-}k)\log(n\mathbin{\dot-}k),$$
--   where $\dot-$ is truncated natural subtraction and all logarithms are real natural logarithms. The prime interval product is the product of primes in $(a,b]$, with empty product 1.
--
--   A finite prime-gap cover with parameters g,L,v recursively requires its current entry p to be prime and at most v+g, and either to reach p>=L or to continue from p. The empty list fails this predicate. A second version has gap 36 and the strict stopping condition p>L. Explicit lists are retained for the numerical ranges used in the chapter. The bounded prime search tests successive integers after m for at most the specified number of steps; when its allowance is exhausted it returns the current integer, so its definition alone does not guarantee a prime output.
--
--   Writing $v_p(m)$ for the natural-number factorization exponents, the two finite products are
--   $$A_\ell(m)=\prod_{p\in\operatorname{supp}(m.\mathrm{factorization})}p^{v_p(m)\bmod\ell},\qquad B_\ell(m)=\prod_{p\in\operatorname{supp}(m.\mathrm{factorization})}p^{\lfloor v_p(m)/\ell\rfloor}.$$
--   For positive ell these specify the remainder and quotient exponents. The definitions use Lean’s natural arithmetic conventions at ell=0 as well. At m=0 the factorization support is empty and both products are 1; no universal decomposition identity for m=0 is asserted here.
-- source:
--   Original definitions: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter03.lean#L52. Topic: Proofs from THE BOOK, 6th edition, Chapter 3, “Binomial coefficients are (almost) never powers” (https://doi.org/10.1007/978-3-662-57265-8_3). The threshold, cover, and power-free definitions are the repository’s concrete mathematical infrastructure.

import Mathlib

/-!
# Chapter 3: Binomial coefficients are (almost) never powers

From "Proofs from THE BOOK" (Aigner & Ziegler).

## Book content summary

The book states Sylvester's theorem (1892):

> If n ≥ 2k, then at least one of the numbers n, n - 1, ..., n - k + 1
> has a prime divisor p greater than k.

Equivalently, the binomial coefficient C(n,k) = n(n-1)...(n-k+1)/k!
always has a prime factor p > k when n ≥ 2k.

The central case n = 2k is precisely Bertrand's postulate (Chapter 2).

For the general case, the book notes (p. 13):

> In 1934, Erdős gave a short and elementary Book Proof of Sylvester's
> result, running along the lines of his proof of Bertrand's postulate.

The book does **not** reproduce this proof in full. It references:

> P. Erdős: A theorem of Sylvester and Schur,
> J. London Math. Soc. 9 (1934), 282-288.

The rest of Chapter 3 uses Sylvester's theorem as a lemma to prove the
"binomial coefficients are almost never powers" result.

## Formalization status

The central case (C(2k,k)) is fully proved below using Bertrand's postulate.

The general case (`sylvester_general`) currently takes `hsmooth` (that
n.descFactorial k is not (k+1)-smooth) as a premise. Eliminating this
premise requires a full formalization of Erdős's 1934 Sylvester-Schur
proof, which uses a refined analysis of how prime powers are distributed
among the k consecutive integers — more delicate than the Bertrand
chapter's global inequality bounding.

This is tracked in TODO.md as "Ch03: Sylvester smoothness core" —
difficulty: Medium-Hard, blocker: needs Erdős 1934 proof formalized.
-/

namespace ProofsInTheBook.Chapter03

open Nat

def HasPrimeFactorAbove (k m : ℕ) : Prop :=
  ∃ p, k < p ∧ p.Prime ∧ p ∣ m

def NoLargePrimeFactor (k m : ℕ) : Prop :=
  ∀ p, p.Prime → p ∣ m → p ≤ k

noncomputable def entropyTerm (n k : ℕ) : ℝ :=
  (n : ℝ) * Real.log n
    - (k : ℝ) * Real.log k
    - ((n - k : ℕ) : ℝ) * Real.log (n - k)

def primeIntervalProduct (a b : ℕ) : ℕ :=
  ∏ p ∈ Finset.Ioc a b with p.Prime, p















































































































































































































































































def PrimeGapCoverWith (gap limit prev : ℕ) : List ℕ → Prop
  | [] => False
  | p :: ps => p.Prime ∧ p ≤ prev + gap ∧ (limit ≤ p ∨ PrimeGapCoverWith gap limit p ps)



def primeGap20Cover : List ℕ :=
  [19, 37, 53, 73, 89, 109, 127, 139, 157, 173, 193, 211, 229, 241, 257, 277, 293, 313, 331, 349, 367, 383, 401, 421, 439, 457, 467, 487, 503, 523, 541, 557, 577, 593, 613, 631, 647, 661, 677, 691, 709, 727, 743, 761, 773, 787, 797, 811, 829, 839, 859, 877, 887, 907, 919, 937, 953, 971, 991, 1009, 1021, 1039, 1051, 1069, 1087, 1103]





def primeGapSmall9Cover : List ℕ :=
  [17, 23, 31, 37, 43, 47, 53, 61, 67, 73]


def primeGapSmall10Cover : List ℕ :=
  [19, 29, 37, 47, 53, 61, 71, 79, 89, 97]


def primeGapSmall11Cover : List ℕ :=
  [19, 29, 37, 47, 53, 61, 71, 79, 89, 97, 107, 113]


def primeGapSmall12_lowCover : List ℕ :=
  [23, 31, 43, 53, 61, 73, 83, 89, 101, 113]


def primeGapSmall12_highCover : List ℕ :=
  [127, 139]


def primeGapSmall13_lowCover : List ℕ :=
  [23, 31, 43, 53, 61, 73, 83, 89, 101, 113]


def primeGapSmall13_highCover : List ℕ :=
  [127, 139, 151, 163]


def primeGapSmall14Cover : List ℕ :=
  [23, 37, 47, 61, 73, 83, 97, 109, 113, 127, 139, 151, 163, 173, 181, 193]


def primeGapSmall15Cover : List ℕ :=
  [29, 43, 53, 67, 79, 89, 103, 113, 127, 139, 151, 163, 173, 181, 193, 199, 211]


def primeGapSmall16Cover : List ℕ :=
  [31, 47, 61, 73, 89, 103, 113, 127, 139, 151, 167, 181, 197, 211, 227, 241]


def primeGapSmall17Cover : List ℕ :=
  [31, 47, 61, 73, 89, 103, 113, 127, 139, 151, 167, 181, 197, 211, 227, 241, 257, 271, 283]


def primeGapSmall18Cover : List ℕ :=
  [31, 47, 61, 79, 97, 113, 131, 149, 167, 181, 199, 211, 229, 241, 257, 271, 283, 293, 311]


def primeGapSmall19Cover : List ℕ :=
  [37, 53, 71, 89, 107, 113, 131, 149, 167, 181, 199, 211, 229, 241, 257, 271, 283, 293, 311, 317, 331, 349]


def primeGapSmall34Cover : List ℕ :=
  [67, 101, 131, 163, 197, 229, 263, 293, 317, 349, 383, 409, 443, 467, 499, 523, 557, 587, 619, 653, 683, 709, 743, 773, 797, 829, 863, 887, 919, 953, 983, 1013, 1039, 1069, 1103, 1129]


def primeGapSmall35Cover : List ℕ :=
  [67, 101, 131, 163, 197, 229, 263, 293, 317, 349, 383, 409, 443, 467, 499, 523, 557, 587, 619, 653, 683, 709, 743, 773, 797, 829, 863, 887, 919, 953, 983, 1013, 1039, 1069, 1103, 1129, 1163, 1193]










def nextPrimeWithin : ℕ → ℕ → ℕ
  | 0, m => m
  | fuel + 1, m => if Nat.Prime (m + 1) then m + 1 else nextPrimeWithin fuel (m + 1)



def primeGap36Cover : List ℕ :=
  [31, 67, 103, 139, 173, 199, 233, 269, 293, 317, 353, 389, 421, 457, 491, 523, 557, 593, 619, 653, 683, 719, 751, 787, 823, 859, 887, 919, 953, 983, 1019, 1051, 1087, 1123, 1153, 1187, 1223, 1259, 1291, 1327, 1361, 1381, 1409, 1439, 1471, 1499, 1531, 1567, 1601, 1637, 1669, 1699, 1733, 1759, 1789, 1823, 1847, 1879, 1913, 1949, 1979, 2011, 2039, 2069, 2099, 2131, 2161, 2179, 2213, 2243, 2273, 2309, 2341, 2377, 2411, 2447, 2477, 2503, 2539, 2557, 2593, 2621, 2657, 2693, 2729, 2753, 2789, 2819, 2851, 2887, 2917, 2953, 2971, 3001, 3037, 3067, 3089, 3121, 3137, 3169, 3203, 3229, 3259, 3271, 3307, 3343, 3373, 3407, 3433, 3469, 3499, 3533, 3559, 3593, 3623, 3659, 3691, 3727, 3761, 3797, 3833, 3863, 3889, 3923, 3947, 3967, 4003, 4027, 4057, 4093, 4129, 4159, 4177, 4211, 4243, 4273, 4297, 4327, 4363, 4397, 4423, 4457, 4493, 4523, 4549, 4583, 4603, 4639, 4673, 4703, 4733, 4759, 4793, 4817, 4831, 4861, 4889, 4919, 4951, 4987, 5023, 5059, 5087, 5119, 5153, 5189, 5209, 5237, 5273, 5309, 5333, 5351, 5387, 5419, 5449, 5483, 5519, 5531, 5563, 5591, 5623, 5659, 5693, 5717, 5749, 5783, 5813, 5849, 5881, 5903, 5939, 5953, 5987, 6011, 6047, 6079, 6113, 6143, 6173, 6203, 6229, 6263, 6299, 6329, 6361, 6397, 6427, 6451, 6481, 6491, 6521, 6553, 6581, 6607, 6637, 6673, 6709, 6737, 6763, 6793, 6829, 6863, 6899, 6917, 6949, 6983, 7019, 7043, 7079, 7109, 7129, 7159, 7193, 7229, 7253, 7283, 7309, 7333, 7369, 7393, 7417, 7451, 7487, 7523, 7559, 7591, 7621, 7649, 7681, 7717, 7753, 7789, 7823, 7853, 7883, 7919, 7951, 7963, 7993, 8017, 8053, 8089, 8123, 8147, 8179, 8209, 8243, 8273, 8297, 8329, 8363, 8389, 8423, 8447, 8467, 8501, 8537, 8573, 8609, 8641, 8677, 8713, 8747, 8783, 8819, 8849, 8867, 8893, 8929, 8963, 8999, 9029, 9059, 9091, 9127, 9161, 9187, 9221, 9257, 9293, 9323, 9349, 9377, 9413, 9439, 9473, 9497, 9533, 9551, 9587, 9623, 9649, 9679, 9697, 9733, 9769, 9803, 9839, 9871, 9907, 9941, 9973, 10009, 10039, 10069, 10103, 10139, 10169, 10193, 10223, 10259, 10289, 10321, 10357, 10391, 10427, 10463, 10499, 10531, 10567, 10601, 10631, 10667, 10691, 10723, 10753, 10789, 10799, 10831, 10867, 10903, 10939, 10973, 11003, 11027, 11059, 11093, 11119, 11149, 11177, 11213, 11243, 11279, 11311, 11329, 11353, 11383, 11411, 11447, 11483, 11519, 11551, 11587, 11621, 11657, 11689, 11719, 11743, 11779, 11813, 11839, 11867, 11903, 11939, 11971, 12007, 12043, 12073, 12109, 12143, 12163, 12197, 12227, 12263, 12289, 12323, 12347, 12379, 12413, 12437, 12473, 12503, 12539, 12569, 12601, 12637, 12671, 12703, 12739, 12763, 12799, 12829, 12853, 12889, 12923, 12959, 12983, 13009, 13043, 13063, 13099, 13127, 13163, 13187, 13219, 13249, 13267, 13297, 13331, 13367, 13399, 13421, 13457, 13487, 13523, 13553, 13577, 13613, 13649, 13681, 13711, 13729, 13763, 13799, 13831, 13859, 13883, 13913, 13933, 13967, 13999, 14033, 14057, 14087, 14107, 14143, 14177, 14207, 14243, 14251, 14281, 14303, 14327, 14347, 14369, 14401]

def PrimeGapCover (limit prev : ℕ) : List ℕ → Prop
  | [] => False
  | p :: ps => p.Prime ∧ p ≤ prev + 36 ∧ (limit < p ∨ PrimeGapCover limit p ps)















/-!
### Central case of Sylvester's theorem

For the central binomial coefficient C(2k,k), we can give a clean proof
using Bertrand's postulate (Chapter 2):
- By Bertrand, ∃ prime p with k < p ≤ 2k.
- p divides (2k)! since p ≤ 2k.
- p does not divide k! since p > k.
- Since C(2k,k) · (k!)² = (2k)!, Euclid's lemma gives p | C(2k,k).
-/



/-!
### General Sylvester's theorem

For n ≥ 2k, the book extends the argument to C(n,k) by analyzing the
product n(n-1)···(n-k+1) = k! · C(n,k). For each of the k consecutive
integers n-j (0 ≤ j ≤ k-1), decompose n-j = q_j · r_j where q_j is
k-smooth and r_j has only prime factors > k. The q_j are bounded by
the prime factorization structure, forcing some r_j > 1.
-/











/-!
### Binomial coefficients are (almost) never powers

Erdős's theorem (1951): C(n,k) ≠ m^l for k ≥ 4, n ≥ 2k, l ≥ 2.
Reference: P. Erdős, On a diophantine equation,
J. London Math. Soc. 26 (1951), 176-178.

Below: Step 1 (concentration lemma + n > k²) is complete.
Steps 2–4 are pending (l-th-power-free decomposition, distinctness,
classification {aⱼ}={1,…,k}, and contradiction for l=2, l≥3).
-/

section Tier1

/-! ### Prime-divisibility helpers for Finset products -/





/-! ### Step 1: Concentration lemma → n > k² -/







/-! ### Step 2: l-th-power-free decomposition -/

/-- The l-th-power-free core of m: for each prime p, retain p^(v_p(m) % l). -/
def lPowerFreePart (l m : ℕ) : ℕ :=
  ∏ p ∈ m.factorization.support, p ^ (m.factorization p % l)

/-- The l-th-power root: p^(v_p(m) / l) per prime, so that
m = (lPowerFreePart l m) * (lPowerRoot l m)^l. -/
def lPowerRoot (l m : ℕ) : ℕ :=
  ∏ p ∈ m.factorization.support, p ^ (m.factorization p / l)



/-! ### 2-power-free part: factorization mod 2 (Tier 2 building block for Ch03) -/





























































































/-! ### Interval count + Legendre / `padicValNat_factorial` helpers (Tier 2 building blocks for Ch03) -/



/-! ### Legendre / `padicValNat_factorial` helpers -/













/-! ### Erdős divisibility step (general l) -/



/-! ### Erdős divisibility step (l = 2 case): discharge of `hprod_l2` -/







/-! ### Main theorem assembly -/




end Tier1

end ProofsInTheBook.Chapter03


