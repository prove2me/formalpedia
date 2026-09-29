-- Prove2me | Theorems.Thm_Bridges_DeepestRungTwoSeed256_mass_lt_bestMass_of_swap
-- name    : Bridges.DeepestRungTwoSeed256.mass_lt_bestMass_of_swap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:37:01.665971+00:00
-- url     : https://prove2.me/theorems/6806724b-ef1f-4da4-8cc9-80fe37bef13c
-- title:
--   Strict selection gap.
-- statement:
--   **Strict selection gap.**  A selection that keeps a key `i` while dropping a strictly
--   heavier key `j` is strictly beaten by the top-`k` selection.  This is the structural reason
--   the repaired random-`k` control of NET-43 had to show a positive gap.
--
--   ```lean
--   theorem Bridges.DeepestRungTwoSeed256.mass_lt_bestMass_of_swap{k : ℕ} (a : AttnDist n) {S : Finset (Fin n)}
--       (hS : S.card ≤ k) {i j : Fin n} (hi : i ∈ S) (hj : j ∉ S) (hlt : a.p i < a.p j) :
--       ∑ x ∈ S, a.p x < bestMass a k := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/DeepestRungTwoSeed256.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/DeepestRungTwoSeed256.lean#L113

-- Thm stub generated from Speculative/AutoResearch/DeepestRungTwoSeed256.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_DeepestRungTwoSeed256
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# The Deepest Rung Is Two-Seed 256: a formal bridge between attention concentration,
# knee brackets, and concave depth laws

This file formalises the *mathematical skeleton* behind the NET-43 measurement round
("the deepest rung is two-seed 256").  The empirical round measured, for a causal
transformer of depth `d = 32` at context `ctx = 512`, the smallest top-`k` attention
width `k` whose accuracy clears a fixed bar, obtaining `k* = 256` at two independent
seeds, with knee bracket `(240, 256]`, effective attention support `≈ 216.92`,
top-`256` attention mass `≈ 0.922`, and a positive random-`k` selection gap.

None of those numbers can be *proved*; they are measurements.  What can be proved —
and is proved here, with no `sorry` — are the structural laws that make the
measurement protocol meaningful, and the arithmetic consequences of the reported
numbers.  Four independent mathematical threads are bridged:

1. **Selection geometry** (`bestMass`).  Top-`k` selection is optimal among all
   width-`k` selections (`mass_le_bestMass`), and *strictly* better than any
   selection that omits a heavier index (`mass_lt_bestMass_of_swap`).  This is the
   theorem behind the "random-`k` control" of Part B2: the measured selection gap
   is nonnegative by mathematics, and strictly positive as soon as the random draw
   misses a heavier key.

2. **Concentration ⇒ knee lower bound** (`card_ge_of_bestMass_ge`).  Via
   Chebyshev/Cauchy–Schwarz, any width `k` reaching mass `τ` obeys
   `k ≥ τ² · eff`, where `eff = 1 / ∑ pᵢ²` is the participation-ratio effective
   support.  Thus the *measured concentration* `eff ≈ 216.92` forces
   `k* > 183` — an independent, purely mathematical corroboration of the measured
   knee `256`, and a refutation of any "knee ≈ 96" style claim at this cell.

3. **Knee brackets and two-seed agreement** (`knee_mem_bracket`,
   `two_seed_knee_eq_of_grid`).  If passing is upward closed in `k`, the knee is the
   least passing width; a fail at `240` and a pass at `256` bracket it in `(240, 256]`;
   and on the NET-43 sweep grid that bracket contains a *unique* grid point, so two
   seeds that both fail at `240` and pass at `256` must report the *same* knee.
   This is the exact-reproduction claim, proved as a lemma about upward-closed
   predicates rather than asserted from data.

4. **Concave depth law** (`kstarLaw`).  The fitted law `k*(d) = 24.7 · d^(2/3)` is
   concave, has per-doubling ratio `2^(2/3) ∈ (1.58, 1.59) < 2` (sub-linear depth
   leg), is subadditive, and — the structural punchline — *any affine model
   calibrated at two shallower depths necessarily over-predicts at every greater
   depth* (`concave_affine_extrapolation_over_predicts`).  The empirical statement
   "the affine model `8d + 32 = 288` over-predicts the measured `256` by more than
   11%" is therefore an instance of a theorem about concavity, not a coincidence.

## Main results

* `mass_le_bestMass`, `mass_lt_bestMass_of_swap` — selection-gap nonnegativity/strictness
* `sq_bestMass_le_card_mul_sumSq` — Chebyshev bound on best-`k` mass
* `card_ge_of_bestMass_ge` — knee lower bound `k ≥ τ² · eff`
* `net43_concentration_forces_knee_gt_183` — the NET-43 instance of the above
* `knee_mem_bracket`, `two_seed_knee_eq_of_grid`, `net43_two_seed_exact`
* `kstarLaw_concaveOn`, `kstarLaw_doubling`, `two_pow_two_thirds_lt_two`,
  `kstarLaw_subadditive`
* `concave_affine_extrapolation_over_predicts`, `net43_affine_over_predicts`
* `net43_speedup_two`, `product_law_no_speedup`
-/

open Bridges.DeepestRungTwoSeed256

open Finset

/-! ## 1. Selection geometry: top-`k` attention mass -/


variable {n : ℕ}

theorem Bridges.DeepestRungTwoSeed256.mass_lt_bestMass_of_swap{k : ℕ} (a : AttnDist n) {S : Finset (Fin n)}
    (hS : S.card ≤ k) {i j : Fin n} (hi : i ∈ S) (hj : j ∉ S) (hlt : a.p i < a.p j) :
    ∑ x ∈ S, a.p x < bestMass a k := by sorry
