-- Prove2me | Theorems.Thm_Bridges_AttentionKneeHeavyTail_spikeRow_knee
-- name    : Bridges.AttentionKneeHeavyTail.spikeRow_knee
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:22:04.749278+00:00
-- url     : https://prove2.me/theorems/1aae8c8c-4bbf-4751-9df8-56c12c9026a0
-- title:
--   At the gate `3/4` the spike row needs exactly `m + 1` keys.
-- statement:
--   At the gate `3/4` the spike row needs exactly `m + 1` keys.
--
--   ```lean
--   theorem Bridges.AttentionKneeHeavyTail.spikeRow_knee{m : ℕ} (hm : 1 ≤ m) :
--       knee (spikeRow m) (3 / 4) = m + 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AttentionKneeHeavyTail.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AttentionKneeHeavyTail.lean#L178

-- Thm stub generated from Bridges/AttentionKneeHeavyTail.lean
import Mathlib
import Definitions.Def_Bridges_AttentionKneeEntropyBound
import Definitions.Def_Bridges_AttentionKneeFlatness
import Definitions.Def_Bridges_AttentionKneeGeometry
import Definitions.Def_Bridges_AttentionKneeHeavyTail
/-
  # Cycle 4: where the collision-entropy floor really fails

  Cycle 2 (`Bridges.AttentionKneeEntropyBound`) proved the Cauchy–Schwarz floor

      `k*(g) ≥ g² / E`,      `E = attention energy (collision probability)`,

  and cycle 3 (`Bridges.AttentionKneeFlatness`) showed that on a *geometric* row
  `w i = (1-a) aⁱ` the floor is tight up to a factor depending on the gate alone,
  uniformly in the decay ratio `a`.  That refuted the conjectured blow-up in `a`
  and raised the obvious follow-up (direction **C6** of `FUTURE_DIRECTIONS.md`):
  is the floor tight for *every* sorted row, or is the bounded-ratio phenomenon
  special to exponential decay?

  This module settles that question in the strong direction: **the floor is not
  tight in general, and the loss is unbounded even at a fixed gate.**  The
  witness is the "spike + plateau" family — one dominant key of weight `1/2`
  followed by `2m` equal keys of weight `1/(4m)` — a genuine sorted probability
  row (`spikeRow_antitone`, `mass_spikeRow_total`):

  * `mass_spikeRow`   — closed-form retention `1/2 + k/(4m)`;
  * `spikeRow_knee`   — at gate `3/4` the knee is exactly `m + 1`, so it grows
    linearly in the plateau length;
  * `energy_spikeRow_le` / `spikeRow_energy_ge_quarter` — the energy stays pinned
    in `[1/4, 1/4 + 1/(8m)]`, i.e. the Rényi-2 entropy never exceeds `2` bits,
    because the spike alone already accounts for a quarter of the energy;
  * `spikeRow_floor_le` — hence the Cauchy–Schwarz floor never exceeds `9/4`
    keys, while the true knee is `m + 1`;
  * `heavyTail_floor_ratio_unbounded` — for every `R` there is such a row whose
    knee exceeds `R` times its energy floor;
  * `entropy_floor_tightness_dichotomy` — the two halves side by side: bounded
    ratio on the whole geometric family, unbounded ratio on the spike family.

  Consequence for the NET-63 thread: an entropy (Rényi-2) measurement alone can
  *never* certify a key budget — it only ever gives a lower bound that can be
  off by an arbitrary factor.  The upper half of the bracket must come from a
  tail/decay hypothesis (cycle 1's `knee_le_of_geometric_tail`), and the
  gate-only constant of cycle 3 is a theorem *about exponential decay*, not a
  universal law.
-/


open Bridges.AttentionKneeHeavyTail

open Finset Bridges.AttentionKneeGeometry Bridges.AttentionKneeEntropyBound
open Bridges.AttentionKneeFlatness

/-! ## 1. The spike-plus-plateau row -/







/-! ## 2. Retention: a linear plateau -/



/-! ## 3. Energy: pinned by the spike -/






/-! ## 4. The knee grows linearly in the plateau length -/

theorem Bridges.AttentionKneeHeavyTail.spikeRow_knee{m : ℕ} (hm : 1 ≤ m) :
    knee (spikeRow m) (3 / 4) = m + 1 := by sorry
