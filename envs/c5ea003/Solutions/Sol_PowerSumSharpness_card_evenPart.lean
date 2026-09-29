-- Prove2me | solution 1 for PowerSumSharpness.card_evenPart
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T01:04:45.603979+00:00
-- url     : https://prove2.me/submissions/ff78a6d0-d119-4e5f-8d71-d94214322bef

-- Sol generated from Shared/PowerSumSharpness.lean
import Mathlib
import Definitions.Def_Shared_PowerSumSharpness

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

lemma mem_ofCounts_le (N : ℕ) (c : ℕ → ℕ) {x : ℕ} (hx : x ∈ ofCounts N c) : x ≤ N := by
  rw [ofCounts] at hx
  obtain ⟨j, hj, hxj⟩ := Multiset.mem_sum.mp hx
  rw [Multiset.eq_of_mem_replicate hxj]
  exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)



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



lemma evenPart_bounded (N : ℕ) : ∀ x ∈ evenPart N, x ≤ N := fun _ hx => mem_ofCounts_le _ _ hx

lemma oddPart_bounded (N : ℕ) : ∀ x ∈ oddPart N, x ≤ N := fun _ hx => mem_ofCounts_le _ _ hx

lemma powerSum_evenPart_sub_oddPart (N k : ℕ) :
    powerSum (evenPart N) k - powerSum (oddPart N) k
      = ∑ j ∈ Finset.range (N + 1), (-1 : ℤ) ^ j * (N.choose j) * (j : ℤ) ^ k := by
  rw [evenPart, oddPart, powerSum_ofCounts, powerSum_ofCounts, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : Even j
  · rw [hj.neg_one_pow]; simp [hj]
  · rw [(Nat.not_even_iff_odd.mp hj).neg_one_pow]; simp [hj]

/-- Below the top index the two parts have identical power sums. -/
theorem powerSum_evenPart_eq_oddPart (N : ℕ) {k : ℕ} (hk : k < N) :
    powerSum (evenPart N) k = powerSum (oddPart N) k := by
  have h := powerSum_evenPart_sub_oddPart N k
  rw [alternating_choose_pow N k hk] at h
  linarith




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








/-! ## The binomial pair also minimises the size of a near miss -/

lemma powerSum_index_zero (s : Multiset ℕ) : powerSum s 0 = (Multiset.card s : ℤ) := by
  simp [powerSum]



/-! ## Bridge to polynomial algebra: `N` power sums determine a split monic polynomial

A multiset `s` of naturals bounded by `N` is the root multiset of the monic integer
polynomial `charPoly s = ∏_{x ∈ s} (X - x)`, and `powerSum s k` is the `k`-th power sum of
its roots — for a diagonal(isable) matrix with spectrum `s`, exactly `tr(A^k)`.  Rigidity
therefore says: the first `N + 1` "traces of powers" pin down the whole spectrum. -/







open PowerSumSharpness in
theorem solution(N : ℕ) (hN : 1 ≤ N) : 2 * Multiset.card (evenPart N) = 2 ^ N := by
  have hcard : (Multiset.card (evenPart N) : ℤ) + (Multiset.card (oddPart N) : ℤ)
      = ((2 : ℤ)) ^ N := by
    have hs : ∑ j ∈ Finset.range (N + 1), (evenPart N).count j = Multiset.card (evenPart N) :=
      Multiset.sum_count_eq_card fun a ha =>
        Finset.mem_range.mpr (by have := evenPart_bounded N a ha; omega)
    have ht : ∑ j ∈ Finset.range (N + 1), (oddPart N).count j = Multiset.card (oddPart N) :=
      Multiset.sum_count_eq_card fun a ha =>
        Finset.mem_range.mpr (by have := oddPart_bounded N a ha; omega)
    have hpt : ∀ j ∈ Finset.range (N + 1),
        (evenPart N).count j + (oddPart N).count j = N.choose j := by
      intro j hj
      have hjN : j ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [evenPart, oddPart, count_ofCounts, count_ofCounts, if_pos hjN, if_pos hjN]
      by_cases hev : Even j <;> simp [hev]
    have : ∑ j ∈ Finset.range (N + 1), ((evenPart N).count j + (oddPart N).count j)
        = 2 ^ N := by
      rw [Finset.sum_congr rfl hpt, Nat.sum_range_choose]
    rw [Finset.sum_add_distrib, hs, ht] at this
    exact_mod_cast congrArg (fun n : ℕ => (n : ℤ)) this
  have hpow : powerSum (evenPart N) 0 = powerSum (oddPart N) 0 :=
    powerSum_evenPart_eq_oddPart N (by omega)
  rw [powerSum_index_zero, powerSum_index_zero] at hpow
  have : (2 : ℤ) * (Multiset.card (evenPart N) : ℤ) = ((2 : ℤ)) ^ N := by
    rw [hpow] at hcard ⊢
    linarith
  exact_mod_cast this
