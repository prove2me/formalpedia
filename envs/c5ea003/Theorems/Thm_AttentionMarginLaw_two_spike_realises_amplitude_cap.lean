-- Prove2me | Theorems.Thm_AttentionMarginLaw_two_spike_realises_amplitude_cap
-- name    : AttentionMarginLaw.two_spike_realises_amplitude_cap
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:59:25.477957+00:00
-- url     : https://prove2.me/theorems/327079af-ccf6-4595-a134-2af29c0a4a18
-- title:
--   Non-vacuity of the amplitude cap.
-- statement:
--   **Non-vacuity of the amplitude cap.**  The hypotheses of
--   `effSupport_le_eight_amplitude` are realised: take the row on `Fin 8` putting
--   mass `1/2` on each of two positions.  Its collision mass is `1/2`, so
--   `N_eff = 2`; with `A·ctx = 1` the head `{0, 1}` has `⌈2⌉₊ = 2` positions and
--   carries mass `1 ≥ 1 - 1/2`, and indeed `2 ≤ 8·1 + 4`.
--
--   ```lean
--   theorem AttentionMarginLaw.two_spike_realises_amplitude_cap:
--       ∃ (s T : Finset (Fin 8)) (p : Fin 8 → ℝ),
--         T ⊆ s ∧ 0 < collision s p ∧ effSupport s p = 2 ∧
--           T.card ≤ ⌈2 * (1 : ℝ)⌉₊ ∧
--           1 - (1 : ℝ) / (⌈2 * (1 : ℝ)⌉₊ : ℝ) ≤ ∑ i ∈ T, p i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/AttentionMarginLaw.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/AttentionMarginLaw.lean#L307

-- Thm stub generated from Probability/AttentionMarginLaw.lean
import Mathlib
import Definitions.Def_Probability_AttentionConcentration
import Definitions.Def_Probability_AttentionCostLaw
import Definitions.Def_Probability_AttentionMarginLaw
import Definitions.Def_Probability_AttentionTruncationOutput
/-
# Cycle three: the margin law, and what the depth drift of `N_eff` can be

This file closes the two conjectures that the second cycle left open in
`FUTURE_DIRECTIONS.md`:

* **C1 — the margin law.**  `AttentionTruncationOutput.retention_threshold` shows
  that a top-`k` truncation keeps the prediction as soon as the retained mass
  `ρ` exceeds `1 - m/(4·L·B)`, where `m` is the logit margin and `L·B` the
  read-out constant.  Combining that threshold with the scale-free tail of
  `AttentionCostLaw.zipfTail` pins the *deficit at the knee* two-sidedly:

  `m/(8·L·B) ≤ 1 - ρ(k*) ≤ m/(4·L·B)`,

  i.e. `1 - ρ(k*) = Θ(m/(L·B))` with explicit constants `1/8` and `1/4`
  (`margin_law_theta`).  The knee itself is antitone in the margin
  (`marginKnee_antitone`) and scales exactly like `1/m`
  (`marginKnee_inverse_scaling`).  At the measured long-context cell the
  certified mass ceiling `ρ ≤ 0.65` turns the margin channel into a falsifiable
  numeric prediction: if the retention threshold is what explains the measured
  `0.985` retained accuracy at `k = 64`, then the held-out logit margin must
  satisfy `m > 1.4·L·B` (`netB_margin_channel_lower_bound`).

* **C2 — is the depth drift of `N_eff` a drift of the Zipf amplitude?**  The
  answer, under the model that produced the law, is **no**.  Two independent
  facts are proved here.  First, a scale-free tail of amplitude `A` *caps* the
  effective support: `N_eff ≤ 8·A·ctx + 4` (`effSupport_le_eight_amplitude`),
  equivalently the concentration measurement bounds the amplitude from below,
  `A·ctx ≥ (N_eff - 4)/8` (`amplitude_ge_of_effSupport`).  Second, a
  depth-*linear* knee forces the amplitude to be exactly `δ/32` at every depth
  (`amplitude_forced_by_depth_linear_knee`), so `A` is depth-independent and the
  product `A(d)·d` is *not* constant but grows linearly in `d`
  (`amplitude_times_depth_not_constant`) — the form conjectured in C2 is
  refuted.  Consequently the model predicts a single depth-independent ceiling
  `N_eff ≤ δ·ctx/4 + 4` (`effSupport_ceiling_depth_independent`), under which
  the measured drift `46.6 → 50.2 → 52.7` sits; and the deepest measured cell
  turns that ceiling into a lower bound on the end-to-end error budget,
  `δ ≥ 1.52` (`netA_budget_lower_bound`).

Everything below is proved from the definitions of the earlier files; the only
imported numbers are the logged values `N_eff = 152.11` (cell B, `d = 4`,
`ctx = 512`) and `N_eff = 52.73` (cell A, `d = 16`, `ctx = 128`).
-/


open AttentionMarginLaw

open Finset AttentionConcentration AttentionCostLaw

/-!
## 1.  The margin law (conjecture C1)
-/








/-!
### Lab note: the margin channel at the measured long-context cell

Cell B (`d = 4`, `ctx = 512`, seed 2): `N_eff = 152.11`, `k* = 64`, retained
accuracy `0.985`.  `AttentionConcentration.retained_mass_at_knee_le` certifies
that at most `0.65` of the attention *mass* survives there.
-/


/-!
## 2.  What the concentration measurement says about the tail amplitude (C2)
-/

variable {ι : Type*}





/-!
## 3.  Depth drift of `N_eff` is not amplitude drift (C2, resolved)
-/

theorem AttentionMarginLaw.two_spike_realises_amplitude_cap:
    ∃ (s T : Finset (Fin 8)) (p : Fin 8 → ℝ),
      T ⊆ s ∧ 0 < collision s p ∧ effSupport s p = 2 ∧
        T.card ≤ ⌈2 * (1 : ℝ)⌉₊ ∧
        1 - (1 : ℝ) / (⌈2 * (1 : ℝ)⌉₊ : ℝ) ≤ ∑ i ∈ T, p i := by sorry
