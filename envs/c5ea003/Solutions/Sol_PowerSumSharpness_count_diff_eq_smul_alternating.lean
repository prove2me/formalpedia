-- Prove2me | solution 1 for PowerSumSharpness.count_diff_eq_smul_alternating
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:06:03.967026+00:00
-- url     : https://prove2.me/submissions/11c70d17-8a91-493e-851f-06bc6f67b4b4

-- Sol generated from Shared/PowerSumSharpness.lean
import Mathlib
import Definitions.Def_Shared_PowerSumSharpness
import Theorems.Thm_PowerSumSharpness_eq_zero_of_powerSums_zero_punctured

/-!
# Power-sum rigidity for bounded multisets, and sharpness of the range `k ≤ N`

Let `s` be a multiset of natural numbers all of whose elements are `≤ N`, and let
`p_k(s) = ∑_{x ∈ s} x ^ k` be its power sums (`powerSum`).  This file proves that the window
`0 ≤ k ≤ N` of power sums determines `s` completely, and that this window is *optimal*:
no shorter initial window works, at any level `N`.

## Main results

* `powerSums_determine` — rigidity: if `s` and `t` are bounded by `N` and `p_k(s) = p_k(t)`
  for all `k ≤ N`, then `s = t`.  The proof turns the multisets into their multiplicity
  vectors on `{0,…,N}` and applies the *dual* Vandermonde injectivity
  (`eq_zero_of_powerSums_zero`), which is obtained by testing the weight functional against
  the Lagrange basis polynomials of the nodes `0,…,N` (algebra ↔ combinatorics bridge).
* `powerSums_not_determined_of_lt` — sharpness: for *every* `N` the truncated window
  `k < N` fails, witnessed by the binomial parity pair `evenPart N` / `oddPart N`
  (multiplicity `C(N,j)` at even, resp. odd, `j ≤ N`).
* `powerSum_evenPart_sub_oddPart_top` — a quantitative form of sharpness: this pair agrees
  for all `k < N` and its power sums differ at `k = N` by *exactly* `(-1)^N · N!`.  The proof
  identifies the alternating binomial sum with the `N`-th forward difference of `x ↦ x^k`
  at `0` (`fwdDiff_pow_at_zero`), so `0` below the top degree and `N!` at it.
* `powerSum_threshold_optimal` — the two statements packaged as a single optimality theorem.
* `infinitely_many_near_misses` — the failure at `k < N` is not isolated: infinitely many
  pairs realise it.
* `powerSums_determine_of_pos`, `powerSums_not_determined_of_lt_pos`,
  `powerSum_threshold_optimal_pos` — the boundary is explained: the index `k = 0` is needed
  *only* because the value `0` is invisible to higher power sums (`zero_index_needed`).
  On positive support `{1,…,N}` the punctured window `1 ≤ k ≤ N` is rigid and optimal.
* `evenPart_two`, `oddPart_two` — the catalog witness `(0,2)` vs `(1,1)` is exactly level `2`
  of the general construction; `level_three_gap` is level `3`.
* `near_miss_classification` — *all* near misses are accounted for: the multiplicity
  difference of any pair agreeing below the top index is an integer multiple of the single
  vector `j ↦ (-1)^j C(N,j)` (the kernel line of the truncated Vandermonde matrix).
* `factorial_dvd_powerSum_gap`, `factorial_le_powerSum_gap`, `factorial_gap_attained` —
  consequently the top-index separation is *quantised*: it is always a multiple of `N !`,
  hence at least `N !` for distinct multisets, and the binomial pair attains `N !` exactly.
  So the sharpness witness of `powerSums_not_determined_of_lt` is extremal, not merely
  existent.
* `two_pow_le_two_mul_card_of_near_miss`, `card_evenPart` — the binomial pair is minimal in
  *size* too: a near miss at level `N ≥ 1` has at least `2^(N-1)` elements, and the binomial
  pair has exactly that many.
* `charPoly_eq_iff_powerSums`, `charPoly_ne_of_powerSums_lt` — the spectral reading: for
  monic integer polynomials split with roots in `{0,…,N}` (equivalently, spectra of
  diagonalisable matrices with eigenvalues in `{0,…,N}`), the first `N + 1` power sums of
  the roots — the traces `tr(A^k)` — determine the polynomial, and `N` of them do not.

## Lab notes (experimental data, see `ComputationalEvidence.md`)

Exhaustive search over all multiplicity vectors on `{0,…,N}` with multiplicities `≤ M`:

| `N` | `M` | pairs agreeing for `k ≤ N` | pairs agreeing for `k ≤ N-1` | first witness |
|-----|-----|---------------------------|------------------------------|---------------|
| 1   | 2   | 0                         | 5                            | `{0}` vs `{1}` |
| 2   | 1   | 0                         | 0                            | (needs multiplicity `2`) |
| 2   | 2   | 0                         | 4                            | `{0,2}` vs `{1,1}` |
| 2   | 3   | 0                         | 18                           | `{0,2}` vs `{1,1}` |
| 3   | 2   | 0                         | 0                            | (needs multiplicity `3`) |
| 3   | 3   | 0                         | 9                            | `{0,2,2,2}` vs `{1,1,1,3}` |

The alternating table `A(N,k) = ∑_j (-1)^j C(N,j) j^k` for `k ≤ N` is strictly lower
triangular with diagonal `(-1)^N N!`: `1, -1, 2, -6, 24, -120, 720, -5040, 40320`
(OEIS A000142 up to sign), matching `alternating_choose_pow` and
`alternating_choose_pow_self`.
-/

open Finset

open PowerSumSharpness



@[simp] lemma powerSum_zero (k : ℕ) : powerSum 0 k = 0 := rfl

@[simp] lemma powerSum_add (s t : Multiset ℕ) (k : ℕ) :
    powerSum (s + t) k = powerSum s k + powerSum t k := by
  simp [powerSum]

@[simp] lemma powerSum_replicate (n j k : ℕ) :
    powerSum (Multiset.replicate n j) k = (n : ℤ) * (j : ℤ) ^ k := by
  simp [powerSum, Multiset.map_replicate, Multiset.sum_replicate]

lemma powerSum_finsetSum {ι : Type*} (u : Finset ι) (f : ι → Multiset ℕ) (k : ℕ) :
    powerSum (∑ i ∈ u, f i) k = ∑ i ∈ u, powerSum (f i) k := by
  classical
  induction u using Finset.induction with
  | empty => simp
  | insert a u ha ih => simp [Finset.sum_insert ha, ih]


lemma count_ofCounts (N : ℕ) (c : ℕ → ℕ) (m : ℕ) :
    (ofCounts N c).count m = if m ≤ N then c m else 0 := by
  classical
  rw [ofCounts, Multiset.count_sum']
  simp only [Multiset.count_replicate]
  rw [Finset.sum_ite_eq' (Finset.range (N + 1)) m c]
  simp

lemma powerSum_ofCounts (N : ℕ) (c : ℕ → ℕ) (k : ℕ) :
    powerSum (ofCounts N c) k = ∑ j ∈ Finset.range (N + 1), (c j : ℤ) * (j : ℤ) ^ k := by
  rw [ofCounts, powerSum_finsetSum]
  simp


lemma eq_ofCounts {N : ℕ} {s : Multiset ℕ} (hs : ∀ x ∈ s, x ≤ N) :
    s = ofCounts N (fun j => s.count j) := by
  classical
  refine Multiset.ext.mpr fun m => ?_
  rw [count_ofCounts]
  by_cases hm : m ≤ N
  · simp [hm]
  · simp only [hm, if_false]
    exact Multiset.count_eq_zero.mpr fun hmem => hm (hs m hmem)


/-! ## The Vandermonde kernel -/


/-! ## Rigidity -/


/-! ## Alternating binomial sums -/

lemma neg_one_pow_sub (N j : ℕ) (h : j ≤ N) :
    (-1 : ℤ) ^ (N - j) = (-1 : ℤ) ^ N * (-1 : ℤ) ^ j := by
  have hN : N - j + j = N := by omega
  have hjj : (-1 : ℤ) ^ j * (-1 : ℤ) ^ j = 1 := by
    rw [← pow_add]
    exact Even.neg_one_pow ⟨j, rfl⟩
  calc (-1 : ℤ) ^ (N - j) = (-1 : ℤ) ^ (N - j) * ((-1 : ℤ) ^ j * (-1 : ℤ) ^ j) := by
        rw [hjj, mul_one]
    _ = (-1 : ℤ) ^ (N - j + j) * (-1 : ℤ) ^ j := by rw [pow_add]; ring
    _ = (-1 : ℤ) ^ N * (-1 : ℤ) ^ j := by rw [hN]

/-- The `N`-th forward difference of `x ↦ x ^ k` at `0`, written as an alternating sum. -/
lemma fwdDiff_pow_at_zero (N k : ℕ) :
    (fwdDiff (1 : ℤ))^[N] (fun r : ℤ => r ^ k) 0
      = (-1 : ℤ) ^ N * ∑ j ∈ Finset.range (N + 1),
          (-1 : ℤ) ^ j * (N.choose j) * (j : ℤ) ^ k := by
  rw [fwdDiff_iter_eq_sum_shift, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h0 : (0 : ℤ) + j • (1 : ℤ) = (j : ℤ) := by simp
  rw [h0, smul_eq_mul, neg_one_pow_sub N j hjN]
  ring

/-- **Vanishing of alternating binomial power sums below the top degree.** -/
lemma alternating_choose_pow (N k : ℕ) (hk : k < N) :
    ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ j * (N.choose j) * (j : ℤ) ^ k = 0 := by
  have h0 : (fwdDiff (1 : ℤ))^[N] (fun r : ℤ => r ^ k) 0 = 0 := by
    rw [fwdDiff_iter_pow_eq_zero_of_lt hk]; rfl
  rw [fwdDiff_pow_at_zero N k] at h0
  rcases mul_eq_zero.mp h0 with h | h
  · exact absurd h (pow_ne_zero _ (by norm_num))
  · exact h


/-! ## The extremal near-miss pair -/










/-! ## Sharpness -/



/-! ## The concrete witness `(0,2)` versus `(1,1)` -/










/-! ## Many near misses -/



/-! ## Positive support: the index `k = 0` is needed only because of the value `0`

The cardinality index `k = 0` in `powerSums_determine` is not an artefact: `zero_index_needed`
shows it cannot be dropped.  The obstruction is *exactly* the value `0`, which is invisible to
all higher power sums.  Once `0` is excluded from the support, the shorter window
`1 ≤ k ≤ N` — again of length `N` — already forces equality, and it is again sharp. -/










/-! ## The extremal gap is exactly `N !`

The binomial pair is not merely *a* witness of sharpness: it is the *cheapest* one.  Any pair
of distinct multisets bounded by `N` whose power sums agree below the top index must have
top-index gap divisible by `N !`, hence of absolute value at least `N !` — the value realised
by `evenPart N` / `oddPart N`.  Structurally: the kernel of the truncated Vandermonde matrix
is the line spanned by `j ↦ (-1)^j C(N,j)`, and the coordinate at `j = 0` is an integer. -/

lemma powerSum_eq_sum_counts_int {N : ℕ} {s : Multiset ℕ} (hs : ∀ x ∈ s, x ≤ N) (k : ℕ) :
    powerSum s k = ∑ j ∈ Finset.range (N + 1), (s.count j : ℤ) * (j : ℤ) ^ k := by
  classical
  conv_lhs => rw [eq_ofCounts hs]
  rw [powerSum_ofCounts]







/-! ## The binomial pair also minimises the size of a near miss -/




/-! ## Bridge to polynomial algebra: `N` power sums determine a split monic polynomial

A multiset `s` of naturals bounded by `N` is the root multiset of the monic integer
polynomial `charPoly s = ∏_{x ∈ s} (X - x)`, and `powerSum s k` is the `k`-th power sum of
its roots — for a diagonal(isable) matrix with spectrum `s`, exactly `tr(A^k)`.  Rigidity
therefore says: the first `N + 1` "traces of powers" pin down the whole spectrum. -/







open PowerSumSharpness in
lemma solution{N : ℕ} {s t : Multiset ℕ}
    (hs : ∀ x ∈ s, x ≤ N) (ht : ∀ x ∈ t, x ≤ N)
    (h : ∀ k < N, powerSum s k = powerSum t k) :
    ∀ j ≤ N, (s.count j : ℤ) - (t.count j : ℤ)
      = ((s.count 0 : ℤ) - (t.count 0 : ℤ)) * ((-1 : ℤ) ^ j * (N.choose j)) := by
  classical
  set lam : ℤ := (s.count 0 : ℤ) - (t.count 0 : ℤ) with hlam
  set w : ℕ → ℤ := fun j => ((s.count j : ℤ) - (t.count j : ℤ))
      - lam * ((-1 : ℤ) ^ j * (N.choose j)) with hw
  have hw0 : w 0 = 0 := by simp [hw, hlam]
  have hwk : ∀ k < N, ∑ j ∈ Finset.range (N + 1), (w j : ℚ) * (j : ℚ) ^ k = 0 := by
    intro k hk
    have hint : ∑ j ∈ Finset.range (N + 1), (w j : ℤ) * (j : ℤ) ^ k = 0 := by
      have hexp : ∀ j, (w j : ℤ) * (j : ℤ) ^ k
          = ((s.count j : ℤ) * (j : ℤ) ^ k - (t.count j : ℤ) * (j : ℤ) ^ k)
            - lam * ((-1 : ℤ) ^ j * (N.choose j) * (j : ℤ) ^ k) := by
        intro j; simp only [hw]; ring
      simp only [hexp]
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        alternating_choose_pow N k hk, ← powerSum_eq_sum_counts_int hs,
        ← powerSum_eq_sum_counts_int ht, h k hk]
      ring
    have := congrArg (fun z : ℤ => (z : ℚ)) hint
    push_cast at this
    simpa using this
  have hzero := eq_zero_of_powerSums_zero_punctured (e := fun j => (w j : ℚ)) (by simp [hw0]) hwk
  intro j hj
  have : (w j : ℚ) = 0 := hzero j hj
  have hwj : w j = 0 := by exact_mod_cast this
  simp only [hw, sub_eq_zero] at hwj
  exact hwj
