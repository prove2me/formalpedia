-- Prove2me | Theorems.Thm_Catalog_Novelty_ZeroFitDialU64_spearmanSq_eq
-- name    : Catalog.Novelty.ZeroFitDialU64.spearmanSq_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:18:22.552994+00:00
-- url     : https://prove2.me/theorems/9300ee0d-52d9-46a8-9668-4ce5da8d39ea
-- title:
--   Tie-attenuation law.
-- statement:
--   **Tie-attenuation law.**  For any tie profile with `n ≥ 2` observations,
--   `ρ² = 1 - 12·Σⱼ(mⱼ³ - mⱼ)/(n³ - n)`.  Nothing about the response enters beyond the
--   assumption that its ranking refines the tie blocks.
--
--   ```lean
--   theorem Catalog.Novelty.ZeroFitDialU64.spearmanSq_eq(L : List ℕ) (h : 2 ≤ L.sum) :
--       spearmanSq L = 1 - 12 * tieCorr L / ((L.sum : ℚ) ^ 3 - L.sum) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ZeroFitDialU64.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ZeroFitDialU64.lean#L261

-- Thm stub generated from Novelty/ZeroFitDialU64.lean
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








/-! ## 2. Tie profiles and the three centred sums

A *tie profile* is the list `L` of block sizes of the tied statistic `T`, listed in
increasing order of the `T`-value; `n = L.sum` is the sample size.  The response
`Y` is assumed to *refine* the blocks: its rank vector `S` is a bijection onto
`{1,…,n}` which, restricted to each block, uses exactly the ranks of that block.
The `T`-side rank vector `R` is the usual midrank vector, constant on blocks. -/

theorem Catalog.Novelty.ZeroFitDialU64.spearmanSq_eq(L : List ℕ) (h : 2 ≤ L.sum) :
    spearmanSq L = 1 - 12 * tieCorr L / ((L.sum : ℚ) ^ 3 - L.sum) := by sorry
