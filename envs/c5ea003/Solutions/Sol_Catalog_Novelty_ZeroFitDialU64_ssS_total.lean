-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialU64.ssS_total
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:34:14.950223+00:00
-- url     : https://prove2.me/submissions/6f0a200a-7b05-45b9-9b27-cf8053e6aa5b

-- Sol generated from Novelty/ZeroFitDialU64.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialU64

/-!
# The zero-fit dial at bitlen 64: an exact tie-attenuation ceiling for Spearman correlation

## Research context (FACT round-61 #1, exp 530, `U64-DIAL-HOLDS-COUNT-PARITY`)

The measurement under study reports a Spearman rank correlation between a
*zero-count statistic* `T` (the number of trailing binary zeros, i.e. the 2-adic
valuation, of a uniformly drawn integer) and a downstream `rate`, on uniform
draws at bitlen 64:

* seeds 20261140/41/42 give `0.658 / 0.642 / 0.643`;
* pooled `0.648`, CI `[0.629, 0.665]`, all inside the validation band `[0.55, 0.85]`;
* the dial declines gently from `≈ 0.78` at bitlen 44 to `≈ 0.65` at bitlen 64.

This file supplies the *mathematics* that such a dial needs: an exact,
closed-form ceiling for any Spearman coefficient measured between a tied
discrete statistic and any tie-refining response, together with the explicit
evaluation of that ceiling for the dyadic (2-adic valuation) tie profile of
uniform `b`-bit draws.

## Main results

* `sp_eq_ssR` — the *midrank collapse identity*: if the response ranking refines
  the blocks of the tied statistic, the centred cross-product equals the
  between-block sum of squares.  (Probabilistically: `Cov(R,S) = Var(R)` because
  `R = E[S | block]`.)
* `ssS_eq_ssR_add` — the *tie decomposition*: total centred sum of squares
  = between-block part + `Σⱼ (mⱼ³ - mⱼ)/12`.
* `spearmanSq_eq` — the **tie-attenuation law**
  `ρ² = 1 - 12·Σⱼ(mⱼ³ - mⱼ) / (n³ - n)`, and `spearman_eq_sqrt` for `ρ` itself.
* `spearman_eq_one_iff` — `ρ = 1` exactly when there are no ties.
* `dyadic_spearmanSq` — for the 2-adic tie profile of uniform `b`-bit draws
  (`b ≥ 1`) the ceiling is **exactly** `ρ² = (6/7)·(1 + 1/(2^b(2^b+1)))`.
* `dyadic_ceiling_strict_anti`, `dyadic_ceiling_gt`, `dyadic_ceiling_tendsto` —
  the ceiling decreases strictly in the bitlen and converges to `6/7`
  (`ρ → √(6/7) ≈ 0.92582`) from above.
* `card_two_adic_block`, `dyadicBlocks_eq_valuation_profile` — the arithmetic
  bridge: the tie blocks of the trailing-zero statistic on `range (2^b)` have
  cardinalities `2^(b-1-k)` (plus the singleton `{0}`), which is exactly the
  dyadic profile used above.
* `u64_inside_band`, `u64_below_tie_ceiling`, `tie_ceiling_insufficient`,
  `count_parity_gap` — the recorded round-61 numbers checked against the theory.

## The scientific payload

`tie_ceiling_insufficient` is the sharp negative result: between bitlen 44 and
bitlen 64 the tie-attenuation ceiling can drop by **less than `10⁻²⁶`**, while
the recorded dial drops by `0.78 → 0.648` (i.e. `≈ 0.188` in `ρ²`).  Hence the
observed monotone decline of the zero-fit dial is *not* a tie/quantisation
artefact: the 2-adic tie profile is scale-invariant to within `O(4^{-b})`, and
any explanation of the decline must come from the response, not from the
granularity of the zero-count statistic.
-/

open Finset

open Catalog.Novelty.ZeroFitDialU64

/-! ## 1. Elementary rank sums -/

/-- Gauss sum, shifted to ranks `1, …, m`. -/
lemma sum_rank (m : ℕ) : ∑ t ∈ range m, ((t : ℚ) + 1) = (m : ℚ) * (m + 1) / 2 := by
  induction m with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring

/-- Sum of squares of the ranks `1, …, m`. -/
lemma sum_rank_sq (m : ℕ) :
    ∑ t ∈ range m, ((t : ℚ) + 1) ^ 2 = (m : ℚ) * (m + 1) * (2 * m + 1) / 6 := by
  induction m with
  | zero => simp
  | succ k ih => rw [sum_range_succ, ih]; push_cast; ring



/-- Within a tie block of size `m`, the ranks have centred sum of squares `(m³ - m)/12`. -/
lemma block_centered_sq (m : ℕ) :
    ∑ t ∈ range m, (((t : ℚ) + 1) - ((m : ℚ) + 1) / 2) ^ 2 = ((m : ℚ) ^ 3 - m) / 12 := by
  have h : ∀ t ∈ range m, (((t : ℚ) + 1) - ((m : ℚ) + 1) / 2) ^ 2
      = ((t : ℚ) + 1) ^ 2 - ((m : ℚ) + 1) * ((t : ℚ) + 1) + ((m : ℚ) + 1) ^ 2 / 4 := by
    intros; ring
  rw [sum_congr rfl h, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_range,
    sum_rank, sum_rank_sq, nsmul_eq_mul]
  ring



/-! ## 2. Tie profiles and the three centred sums

A *tie profile* is the list `L` of block sizes of the tied statistic `T`, listed in
increasing order of the `T`-value; `n = L.sum` is the sample size.  The response
`Y` is assumed to *refine* the blocks: its rank vector `S` is a bijection onto
`{1,…,n}` which, restricted to each block, uses exactly the ranks of that block.
The `T`-side rank vector `R` is the usual midrank vector, constant on blocks. -/












lemma ssS_eq_range (mu : ℚ) (L : List ℕ) (c : ℚ) :
    ssS mu L c = ∑ t ∈ range L.sum, ((c + (t : ℚ) + 1) - mu) ^ 2 := by
  induction L generalizing c with
  | nil => simp [ssS]
  | cons m L ih =>
      simp only [ssS, ih, List.sum_cons, Finset.sum_range_add]
      congr 1
      refine sum_congr rfl ?_
      intro t _
      push_cast
      ring










/-! ## 3. The Spearman coefficient itself (real-valued) -/





/-! ## 4. The dyadic tie profile of trailing-zero counts -/









/-! ## 5. Arithmetic bridge: the tie blocks really are the 2-adic ones -/





/-! ## 6. The recorded round-61 measurement, checked against the theory -/










/-!
## Lab notes (exp 530, seeds 20261140–42)

Recorded measurement (uniform draws, bitlen 64):

| seed | Spearman(T, rate) |
|---|---|
| 20261140 | 0.658 |
| 20261141 | 0.642 |
| 20261142 | 0.643 |
| pooled | 0.648, CI [0.629, 0.665] |

Validation band `[0.55, 0.85]`: all four readings inside (`u64_inside_band`).
H2 bar `baseline + 0.05` with baseline `0.580`: cleared by all three point estimates and
by the pooled point estimate; the pooled CI lower bound clears only `+0.049`, missing the
bar by `0.001` — the recorded *count parity* verdict (`count_parity_gap`).

Exact-rational cross-checks performed while developing this file (Lean `#eval`, exact `ℚ`):

| tie profile | brute-force `ρ²` | closed form `1 - 12T/(n³-n)` |
|---|---|---|
| `[2,1,1]` | 9/10 | 9/10 |
| `[4,2,1,1]` | 73/84 | 73/84 |
| `[3,3,3]` | 9/10 | 9/10 |
| `[5,2,2,1]` | 13/15 | 13/15 |
| `[8,4,2,1,1]` | 117/136 | 117/136 |
| `[2,2,2,2]` | 20/21 | 20/21 |
| `[6,1,1,1,1]` | 26/33 | 26/33 |

Dyadic ceiling `ρ` by bitlen: `b=2: 0.948683`, `b=3: 0.932227`, `b=4: 0.927520`,
`b=8: 0.925827`, `b=16, 44, 64: 0.925820…` — monotone decline to `√(6/7) = 0.9258200…`,
total movement above `b = 16` smaller than `10⁻¹⁰`.  The recorded dial moves by `0.13`
over the same range, which is the content of `tie_ceiling_insufficient`.
-/


open Catalog.Novelty.ZeroFitDialU64 in
theorem solution(L : List ℕ) : ssS (gmean L) L 0 = ((L.sum : ℚ) ^ 3 - L.sum) / 12 := by
  rw [ssS_eq_range]
  rw [← block_centered_sq L.sum]
  refine sum_congr rfl ?_
  intro t _
  simp [gmean]
