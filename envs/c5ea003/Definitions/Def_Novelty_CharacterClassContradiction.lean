-- Prove2me | Definitions.Def_Novelty_CharacterClassContradiction
-- name    : Novelty_CharacterClassContradiction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:30.341551+00:00
-- url     : https://prove2.me/theorems/7eda00b5-299d-426e-8010-2e8065af758d
-- title:
--   Aether Catalog definitions — Novelty_CharacterClassContradiction
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.CharacterClassContradiction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/CharacterClassContradiction.lean by skeleton subtraction
import Mathlib

/-!
# The Character Class Contradiction

This file formalises a small "zeta-function" computation for the rank-one matrix

`A = !![1,1;1,1]`

over `ℚ`, and uses it to refute the *naive expectation* that the point counts
`Nᵣ = trace (Aʳ)` should vanish for all `r ≠ 1`.

The matrix `A` has eigenvalues `0` and `2`, so `trace (Aʳ) = 0ʳ + 2ʳ`.  For
`r ≥ 1` this equals `2ʳ`, while for `r = 0` it equals `trace (1) = 2 ≠ 2⁰ = 1`.

## Main results

* `A_mul_A_eq_two_mul_A` — `A * A = 2 • A`.
* `trace_pow_two_shift` — `trace (Aʳ) = 2ʳ` for `r ≥ 1`.
* `det_one_sub_t_mul_A` — `det (1 - t • A) = 1 - 2 t`.
* `zeta_function` — the zeta series `Z t = exp (∑ Nᵣ tʳ / r)` equals
  `1 / (1 - 2 t)` (for `|t| < 1/2`, where the defining series converges).
* `naive_expectation_false` — it is **not** the case that `trace (Aʳ) = 0`
  for all `r ≠ 1`.

## Implementation notes

* The matrix-multiplication notation `⬝` used in older Mathlib has been removed;
  square-matrix multiplication is the ordinary `*`, which is what we use.
* `trace_pow_two_shift` is stated with the hypothesis `1 ≤ r`.  This is necessary:
  at `r = 0` the literal identity `trace (A⁰) = 2⁰` is false because
  `trace (1) = 2` while `2⁰ = 1`.  The zeta series only ever sees the `r ≥ 1`
  values (the `r = 0` summand is killed by the `/ r` with `r = 0`).
* `zeta_function` carries the hypothesis `|t| < 1/2`, the radius of convergence of
  the defining logarithmic series; outside this disc the series diverges, so the
  identity cannot hold for *all* rational `t`.
-/

open Matrix

/-- The rank-one all-ones `2 × 2` matrix over `ℚ`. -/
abbrev A : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 1, 1]






/-- The point counts `Nᵣ = trace (A ^ r)`. -/
noncomputable def N (r : ℕ) : ℚ := (A ^ r).trace

/-- The (exponential) zeta function `Z t = exp (∑ Nᵣ tʳ / r)`.

The `r = 0` term of the sum is `N₀ · t⁰ / 0 = 0` (division by `0` is `0` in
`ℝ`), so only the `r ≥ 1` contributions matter. -/
noncomputable def Z (t : ℚ) : ℝ := Real.exp (∑' r : ℕ, (N r : ℝ) * (t : ℝ) ^ r / r)


