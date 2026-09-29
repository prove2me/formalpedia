-- Prove2me | Theorems.Thm_PowerSumSharpness_eq_zero_of_powerSums_zero_punctured
-- name    : PowerSumSharpness.eq_zero_of_powerSums_zero_punctured
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:25:34.677148+00:00
-- url     : https://prove2.me/theorems/48fc1216-6b66-4826-bc09-da62e00710d1
-- title:
--   Eq zero of power sums zero punctured
-- statement:
--   Formal statement of `PowerSumSharpness.eq_zero_of_powerSums_zero_punctured` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem PowerSumSharpness.eq_zero_of_powerSums_zero_punctured{N : ℕ} {e : ℕ → ℚ} (h0 : e 0 = 0)
--       (h : ∀ k < N, ∑ j ∈ Finset.range (N + 1), e j * (j : ℚ) ^ k = 0) :
--       ∀ m ≤ N, e m = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/PowerSumSharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/PowerSumSharpness.lean#L564

-- Thm stub generated from Shared/PowerSumSharpness.lean
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












/-! ## The Vandermonde kernel -/


/-! ## Rigidity -/


/-! ## Alternating binomial sums -/





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

theorem PowerSumSharpness.eq_zero_of_powerSums_zero_punctured{N : ℕ} {e : ℕ → ℚ} (h0 : e 0 = 0)
    (h : ∀ k < N, ∑ j ∈ Finset.range (N + 1), e j * (j : ℚ) ^ k = 0) :
    ∀ m ≤ N, e m = 0 := by sorry
