-- Prove2me | Theorems.Thm_NumberTheory_ExclusiveChannel_zeroAll_margin_ge_of_redundant
-- name    : NumberTheory.ExclusiveChannel.zeroAll_margin_ge_of_redundant
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:30:49.204334+00:00
-- url     : https://prove2.me/theorems/0f501d5e-d2dc-45b4-88ea-43cf16d4ce0d
-- title:
--   Redundancy upgrade.
-- statement:
--   **Redundancy upgrade.**  If each single-coordinate ablation keeps the margin
--   above threshold `θ` and the block's net contribution is nonpositive, then the
--   whole-block ablation keeps the margin above `θ` as well.
--
--   ```lean
--   theorem NumberTheory.ExclusiveChannel.zeroAll_margin_ge_of_redundant{b θ : ℝ} {g c : Fin k → ℝ} (hk : 0 < k)
--       (hred : ∀ i, θ ≤ margin b g (zeroAt i c)) (hblock : ∑ i, g i * c i ≤ 0) :
--       θ ≤ margin b g (zeroAll c) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/ExclusiveChannelInterventions.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/ExclusiveChannelInterventions.lean#L287

-- Thm stub generated from NumberTheory/ExclusiveChannelInterventions.lean
import Mathlib
import Definitions.Def_NumberTheory_ExclusiveChannelInterventions
/-
# NET-30 / Catalog·NumberTheory — Exclusive boundary channels: interventions, the
k = 1 collapse, and the affine no-go

Formal counterpart of the *intervention algebra* underlying the round-net-30 law
**INTERNALIZATION-SATURATES-AT-K=2**.

In the experiment a trained recurrent cell owns `k` *exclusive* coordinates
(the coordinates of the hidden state that only the end-of-sequence/boundary
pathway writes into).  At inference time one manipulates the stored coefficient
vector `c ∈ ℝ^k` on those coordinates and re-evaluates:

| intervention | action on `c`                       |
|--------------|--------------------------------------|
| `ctl`        | `c`                                  |
| `zeroAll`    | `0` (whole exclusive block frozen)   |
| `zeroAt i`   | `c` with the `i`-th entry set to `0` |
| `flipAt i`   | `c` with the `i`-th entry negated    |
| `scaleAll l` | `l • c`                              |

The measured s = 13, k = 2 arm has the signature

```
ctl 0.9980 | zeroAt 0 : 0.9961 | zeroAt 1 : 0.9990 | zeroAll : 0.7544
           | flipAt 0 : 0.7505 | scaleAll 0.1 : 0.9067
```

i.e. **every single-coordinate ablation is a no-op while the whole-block
ablation costs 0.24**, and the sign flip costs just as much.  This file proves
what that signature can and cannot mean.

* `zeroAt_eq_zeroAll_of_one`, `two_le_of_redundant_and_block_dependent`:
  a *model-free* theorem.  For `k = 1` the interventions `zeroAt 0` and
  `zeroAll` are literally the same map, so **no statistic whatsoever** can
  separate them; for `k = 0` `zeroAll` is the identity.  Hence the
  "1-redundant but block-dependent" signature *forces* `k ≥ 2`.  This is the
  formal content of "the missing middle": the phenomenon is invisible at
  `k = 1` for structural, not empirical, reasons.
* `dropZeroAll_eq_sum_dropZeroAt`, `dropFlipAt_eq_two_mul_dropZeroAt`,
  `dropScaleAll_eq`: in an **affine** read-out the whole intervention algebra
  collapses to one number per coordinate: whole-block drop = sum of the
  single-coordinate drops, flip drop = twice the zero drop, scale-`l` drop =
  `(1 - l)` times the block drop.
* `abs_dropZeroAll_le`, `card_lower_bound_of_block_drop`: the resulting
  quantitative bound — with single-coordinate no-op tolerance `ε` an affine
  read-out can lose at most `k · ε` from the whole block, so an observed block
  drop `D` certifies `k ≥ D / ε` exclusive dimensions.
* `s13_k2_no_affine_readout`, `s13_k2_flip_no_affine_readout`: applied to the
  published s = 13 numbers this is a **no-go**: no affine boundary read-out
  reproduces the measured k = 2 arm (it would need ≥ 128 exclusive dimensions).
  The saturation law is therefore a statement about a *nonlinear* read-out;
  a matching nonlinear realisation is built in
  `NumberTheory.ExclusiveChannelPopulation`, and the exact convexity boundary
  is located in `NumberTheory.ExclusiveChannelConvexity`.
* `zeroAll_margin_ge_of_redundant`: the positive half — if the block's net
  affine contribution is nonpositive ("removal helps", the measured s = 10
  arm), single-coordinate redundancy *does* upgrade to whole-block
  self-sufficiency.
-/


open NumberTheory.ExclusiveChannel

open Finset

variable {k : ℕ}

/-! ## The intervention maps -/










/-! ## The k = 1 collapse (model-free) -/





/-! ## The affine read-out -/






/-! ## Intervention drops in the affine model -/












/-! ## The no-go for the measured k = 2, s = 13 arm

The published numbers are `ctl 0.9980`, `zeroAt 0 : 0.9961`, `zeroAt 1 : 0.9990`
(both inside the reported no-op band `|Δ| ≤ 0.002`), `zeroAll : 0.7544`
(a drop of `0.2436`) and `flipAt 0 : 0.7505` (a drop of `0.2475`).  Reading the
measured accuracies as an affine margin statistic, both signatures are
impossible at `k = 2`. -/



/-! ## The positive half: when redundancy does upgrade

The five self-sufficient k = 2 arms (seeds 8–12) show whole-block drops of at
most `0.010`, and at the imperfect s = 10 arm the block drop is *negative*
(removal helps: `0.9399 → 0.9453`).  Affinely, a nonpositive net block
contribution is exactly the condition under which single-coordinate redundancy
upgrades to whole-block self-sufficiency. -/

theorem NumberTheory.ExclusiveChannel.zeroAll_margin_ge_of_redundant{b θ : ℝ} {g c : Fin k → ℝ} (hk : 0 < k)
    (hred : ∀ i, θ ≤ margin b g (zeroAt i c)) (hblock : ∑ i, g i * c i ≤ 0) :
    θ ≤ margin b g (zeroAll c) := by sorry
