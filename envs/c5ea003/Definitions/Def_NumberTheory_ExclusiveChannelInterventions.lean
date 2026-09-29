-- Prove2me | Definitions.Def_NumberTheory_ExclusiveChannelInterventions
-- name    : NumberTheory_ExclusiveChannelInterventions
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:07:14.9274+00:00
-- url     : https://prove2.me/theorems/4f04c14d-fa08-49e8-83d0-0c30c63e043e
-- title:
--   Aether Catalog definitions — NumberTheory_ExclusiveChannelInterventions
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.ExclusiveChannelInterventions`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/ExclusiveChannelInterventions.lean by skeleton subtraction
import Mathlib
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


namespace NumberTheory.ExclusiveChannel

open Finset

variable {k : ℕ}

/-! ## The intervention maps -/

/-- `zeroAt i` freezes the `i`-th exclusive coordinate to `0`. -/
def zeroAt (i : Fin k) (c : Fin k → ℝ) : Fin k → ℝ := Function.update c i 0

/-- `zeroAll` freezes the whole exclusive block. -/
def zeroAll (_c : Fin k → ℝ) : Fin k → ℝ := fun _ => 0

/-- `flipAt i` negates the `i`-th exclusive coordinate. -/
def flipAt (i : Fin k) (c : Fin k → ℝ) : Fin k → ℝ := Function.update c i (-c i)

/-- `scaleAll l` rescales the whole exclusive block by `l`. -/
def scaleAll (l : ℝ) (c : Fin k → ℝ) : Fin k → ℝ := fun i => l * c i






/-! ## The k = 1 collapse (model-free) -/





/-! ## The affine read-out -/

/-- The affine boundary margin: baseline `b` plus the exclusive block's
contribution `∑ i, g i * c i`, where `g` collects the read-out weights of the
exclusive coordinates. -/
def margin (b : ℝ) (g c : Fin k → ℝ) : ℝ := b + ∑ i, g i * c i





/-! ## Intervention drops in the affine model -/

/-- Accuracy/margin loss caused by freezing the whole exclusive block. -/
def dropZeroAll (b : ℝ) (g c : Fin k → ℝ) : ℝ := margin b g c - margin b g (zeroAll c)

/-- Margin loss caused by freezing the single coordinate `i`. -/
def dropZeroAt (b : ℝ) (g c : Fin k → ℝ) (i : Fin k) : ℝ :=
  margin b g c - margin b g (zeroAt i c)

/-- Margin loss caused by flipping the sign of the single coordinate `i`. -/
def dropFlipAt (b : ℝ) (g c : Fin k → ℝ) (i : Fin k) : ℝ :=
  margin b g c - margin b g (flipAt i c)

/-- Margin loss caused by rescaling the whole block by `l`. -/
def dropScaleAll (b : ℝ) (g c : Fin k → ℝ) (l : ℝ) : ℝ :=
  margin b g c - margin b g (scaleAll l c)








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


end NumberTheory.ExclusiveChannel


