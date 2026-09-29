-- Prove2me | Definitions.Def_Novelty_ZeroFitDialU64
-- name    : Novelty_ZeroFitDialU64
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:54:37.203911+00:00
-- url     : https://prove2.me/theorems/2a3fcd3c-0c52-40e7-8849-6eb5b5b90b08
-- title:
--   Aether Catalog definitions — Novelty_ZeroFitDialU64
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ZeroFitDialU64`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ZeroFitDialU64.lean by skeleton subtraction
import Mathlib

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

namespace Catalog.Novelty.ZeroFitDialU64

/-! ## 1. Elementary rank sums -/








/-! ## 2. Tie profiles and the three centred sums

A *tie profile* is the list `L` of block sizes of the tied statistic `T`, listed in
increasing order of the `T`-value; `n = L.sum` is the sample size.  The response
`Y` is assumed to *refine* the blocks: its rank vector `S` is a bijection onto
`{1,…,n}` which, restricted to each block, uses exactly the ranks of that block.
The `T`-side rank vector `R` is the usual midrank vector, constant on blocks. -/

/-- Between-block (midrank) centred sum of squares, `n · Var R`, with block offset `c`. -/
def ssR (mu : ℚ) : List ℕ → ℚ → ℚ
  | [], _ => 0
  | m :: L, c => (m : ℚ) * ((c + ((m : ℚ) + 1) / 2) - mu) ^ 2 + ssR mu L (c + m)

/-- Total centred sum of squares of the raw ranks, `n · Var S`. -/
def ssS (mu : ℚ) : List ℕ → ℚ → ℚ
  | [], _ => 0
  | m :: L, c => (∑ t ∈ range m, ((c + (t : ℚ) + 1) - mu) ^ 2) + ssS mu L (c + m)

/-- Centred cross product of midranks against raw ranks, `n · Cov (R, S)`. -/
def sp (mu : ℚ) : List ℕ → ℚ → ℚ
  | [], _ => 0
  | m :: L, c =>
      (∑ t ∈ range m, ((c + ((m : ℚ) + 1) / 2) - mu) * ((c + (t : ℚ) + 1) - mu)) + sp mu L (c + m)

/-- The Kendall tie correction `Σⱼ (mⱼ³ - mⱼ)/12`. -/
def tieCorr (L : List ℕ) : ℚ := (L.map fun m => ((m : ℚ) ^ 3 - m) / 12).sum










/-- The grand mean of the ranks `1, …, n`. -/
def gmean (L : List ℕ) : ℚ := ((L.sum : ℚ) + 1) / 2


/-- The squared Spearman coefficient of a tie profile: `Cov(R,S)² / (Var R · Var S)`,
which by `sp_eq_ssR` equals `Var R / Var S`. -/
def spearmanSq (L : List ℕ) : ℚ := ssR (gmean L) L 0 / ssS (gmean L) L 0






/-! ## 3. The Spearman coefficient itself (real-valued) -/

/-- Spearman's rank correlation `Cov(R,S)/(σ_R σ_S)` of a tie profile against a refining
response. -/
noncomputable def spearman (L : List ℕ) : ℝ :=
  (sp (gmean L) L 0 : ℝ) /
    (Real.sqrt ((ssR (gmean L) L 0 : ℚ) : ℝ) * Real.sqrt ((ssS (gmean L) L 0 : ℚ) : ℝ))




/-! ## 4. The dyadic tie profile of trailing-zero counts -/

/-- Tie profile of the trailing-zero statistic on `{0, …, 2^b - 1}`:
blocks of sizes `2^(b-1), 2^(b-2), …, 2, 1` followed by the singleton `{0}`. -/
def dyadicBlocks : ℕ → List ℕ
  | 0 => [1]
  | b + 1 => 2 ^ b :: dyadicBlocks b








/-! ## 5. Arithmetic bridge: the tie blocks really are the 2-adic ones -/

/-- The `k`-th trailing-zero block of `{0, …, 2^b - 1}`. -/
def twoAdicBlock (b k : ℕ) : Finset ℕ :=
  (range (2 ^ b)).filter fun x => 2 ^ k ∣ x ∧ ¬ 2 ^ (k + 1) ∣ x




/-! ## 6. The recorded round-61 measurement, checked against the theory -/

/-- Recorded Spearman values (three seeds and the pooled estimate) at bitlen 64. -/
def seed40 : ℚ := 658 / 1000
def seed41 : ℚ := 642 / 1000
def seed42 : ℚ := 643 / 1000
def pooled : ℚ := 648 / 1000
def ciLow : ℚ := 629 / 1000
def ciHigh : ℚ := 665 / 1000
/-- The bitlen-44 anchor of the validation grid. -/
def dial44 : ℚ := 78 / 100









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

end Catalog.Novelty.ZeroFitDialU64


