-- Prove2me | solution 1 for Bridges.DeepestRungTwoSeed256.mass_lt_bestMass_of_swap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T04:57:52.234252+00:00
-- url     : https://prove2.me/submissions/cf851cca-d365-43ec-b520-fb2b4a45e334

-- Sol generated from Speculative/AutoResearch/DeepestRungTwoSeed256.lean
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



lemma mem_Kset {k : ℕ} {S : Finset (Fin n)} : S ∈ Kset n k ↔ S.card ≤ k := by
  simp [Kset]


/-- **Selection-gap nonnegativity.**  No width-`k` selection — in particular no random-`k`
control — captures more mass than the top-`k` selection. -/
lemma mass_le_bestMass {k : ℕ} (a : AttnDist n) {S : Finset (Fin n)} (hS : S.card ≤ k) :
    ∑ i ∈ S, a.p i ≤ bestMass a k :=
  Finset.le_sup' (fun S => ∑ i ∈ S, a.p i) (mem_Kset.2 hS)





/-! ## 2. Concentration forces a knee lower bound -/







/-! ## 3. Knees, brackets, and two-seed agreement -/












/-! ## 4. The concave depth law `k*(d) = C · d^(2/3)` -/
















/-! ## 5. Cost model and deployable speedup -/






/-! ## 6. Lab notes (NET-43 measured data, round-net-43)

Harness: CausalTF `d_model = 64`, 4 heads, Gutenberg corpus, vocab 4097, 2000 AdamW steps,
depth `d = 32`, context `ctx = 512`, seed 2 (byte-identical to NET-42's seed-1 harness).

| quantity                     | seed 1 (NET-42) | seed 2 (NET-43) |
|------------------------------|-----------------|-----------------|
| full accuracy                | 0.1353          | 0.1350          |
| full loss                    | 5.6281          | 5.6482          |
| accuracy bar (0.98 × full)   | —               | 0.1323          |
| knee `k*`                    | 256             | 256             |
| knee bracket                 | (224, 256]      | (240, 256]      |
| effective support `eff`      | 218.46          | 216.92          |
| top-256 mass                 | 0.921           | 0.922           |
| random-`k` gap at `k = 256`  | (crash)         | +2.6            |
| random-`k` gap at `k = 384`  | (crash)         | +1.7            |
| `k = 512` accuracy ratio     | 1.000           | 1.000           |

Sweep grid: `{96, 128, 160, 192, 224, 240, 256, 288, 320, 384, 512}` (`sweep` above).
Concave-power fit: `k*(d) ≈ 24.7 · d^(2/3)`, predicting `249` at `d = 32`
(`net43_law_prediction_at_32`, `net43_law_within_three_percent`).
Affine fit `8d + 32 = 288` over-predicts (`net43_affine_over_predicts`), which
`net43_affine_calibration_over_predicts` shows to be forced by concavity.
Deployable speedup `512 / 256 = 2.0×` (`net43_speedup_two`).
-/


open Bridges.DeepestRungTwoSeed256 in
theorem solution{k : ℕ} (a : AttnDist n) {S : Finset (Fin n)}
    (hS : S.card ≤ k) {i j : Fin n} (hi : i ∈ S) (hj : j ∉ S) (hlt : a.p i < a.p j) :
    ∑ x ∈ S, a.p x < bestMass a k := by
  classical
  set T : Finset (Fin n) := insert j (S.erase i) with hT
  have hjT : j ∉ S.erase i := fun h => hj (Finset.mem_of_mem_erase h)
  have hcardT : T.card ≤ k := by
    have h1 : T.card = (S.erase i).card + 1 := by
      rw [hT, Finset.card_insert_of_notMem hjT]
    have h2 : (S.erase i).card = S.card - 1 := Finset.card_erase_of_mem hi
    have h3 : 1 ≤ S.card := Finset.card_pos.2 ⟨i, hi⟩
    omega
  have hsumT : ∑ x ∈ T, a.p x = a.p j + ∑ x ∈ S.erase i, a.p x := by
    rw [hT, Finset.sum_insert hjT]
  have hsumS : ∑ x ∈ S, a.p x = a.p i + ∑ x ∈ S.erase i, a.p x :=
    (Finset.add_sum_erase _ _ hi).symm
  have := mass_le_bestMass a hcardT
  rw [hsumT] at this
  linarith
