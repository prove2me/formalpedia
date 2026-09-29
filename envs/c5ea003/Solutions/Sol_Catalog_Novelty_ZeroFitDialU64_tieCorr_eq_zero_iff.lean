-- Prove2me | solution 1 for Catalog.Novelty.ZeroFitDialU64.tieCorr_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T19:48:18.314629+00:00
-- url     : https://prove2.me/submissions/50a3a394-f826-408e-a61e-d1e284431dff

-- Sol generated from Novelty/ZeroFitDialU64.lean
import Mathlib
import Definitions.Def_Novelty_ZeroFitDialU64
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_cube_sub_self_pos
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_tieCorr_cons
import Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_tieCorr_nonneg

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



/-- `x³ - x ≥ 0` for `x ≥ 1`. -/
lemma cube_sub_self_nonneg {x : ℚ} (h : 1 ≤ x) : 0 ≤ x ^ 3 - x := by
  have h1 : (0 : ℚ) ≤ x * (x - 1) * (x + 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  linarith [h1]





/-! ## 2. Tie profiles and the three centred sums

A *tie profile* is the list `L` of block sizes of the tied statistic `T`, listed in
increasing order of the `T`-value; `n = L.sum` is the sample size.  The response
`Y` is assumed to *refine* the blocks: its rank vector `S` is a bijection onto
`{1,…,n}` which, restricted to each block, uses exactly the ranks of that block.
The `T`-side rank vector `R` is the usual midrank vector, constant on blocks. -/






/-- Each tie-correction term is nonnegative. -/
lemma tieCorr_term_nonneg (m : ℕ) : 0 ≤ ((m : ℚ) ^ 3 - m) / 12 := by
  rcases Nat.eq_zero_or_pos m with hz | hz
  · simp [hz]
  · have h1 : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hz
    have := cube_sub_self_nonneg h1
    linarith

/-- A block of size at least two contributes strictly. -/
lemma tieCorr_term_pos {m : ℕ} (h : 2 ≤ m) : 0 < ((m : ℚ) ^ 3 - m) / 12 := by
  have h1 : (2 : ℚ) ≤ (m : ℚ) := by exact_mod_cast h
  have := cube_sub_self_pos h1
  linarith















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
theorem solution(L : List ℕ) : tieCorr L = 0 ↔ ∀ m ∈ L, m ≤ 1 := by
  induction L with
  | nil => simp [tieCorr]
  | cons m L ih =>
      rw [tieCorr_cons]
      constructor
      · intro h
        have h2 := tieCorr_nonneg L
        have hm : 0 ≤ ((m : ℚ) ^ 3 - m) / 12 := tieCorr_term_nonneg m
        have hm0 : ((m : ℚ) ^ 3 - m) / 12 = 0 := by linarith
        have hL0 : tieCorr L = 0 := by linarith
        have hmle : m ≤ 1 := by
          by_contra hc
          push_neg at hc
          have := tieCorr_term_pos hc
          linarith
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx'
        · exact hmle
        · exact (ih.1 hL0) x hx'
      · intro h
        have hm : m ≤ 1 := h m (List.mem_cons_self ..)
        have hL : tieCorr L = 0 := ih.2 fun x hx => h x (List.mem_cons_of_mem _ hx)
        interval_cases m <;> simp [hL]
