-- Prove2me | Theorems.Thm_Bridges_AttentionKneeFlatness_geoRow_ratio_blowup_refuted
-- name    : Bridges.AttentionKneeFlatness.geoRow_ratio_blowup_refuted
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:21:16.73426+00:00
-- url     : https://prove2.me/theorems/37183343-e02a-4c86-a6fd-a672307b31ed
-- title:
--   Restated as the explicit refutation of "the ratio grows without bound":
-- statement:
--   Restated as the explicit refutation of "the ratio grows without bound":
--   there is a single constant, depending on the gate alone, that dominates the
--   knee-to-floor ratio for *every* geometric row.
--
--   ```lean
--   theorem Bridges.AttentionKneeFlatness.geoRow_ratio_blowup_refuted{g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) :
--       ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a < 1 →
--         (knee (geoRow a) g : ℝ) ≤ C * (g ^ 2 / geoEnergy a) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/AttentionKneeFlatness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/AttentionKneeFlatness.lean#L221

-- Thm stub generated from Bridges/AttentionKneeFlatness.lean
import Mathlib
import Definitions.Def_Bridges_AttentionKneeEntropyBound
import Definitions.Def_Bridges_AttentionKneeFlatness
import Definitions.Def_Bridges_AttentionKneeGeometry
/-
  # Cycle 3: the flatness dichotomy for the Cauchy–Schwarz knee floor

  `Bridges.AttentionKneeGeometry` gives order/grid control of the retention knee
  `k*(g)`, and `Bridges.AttentionKneeEntropyBound` gives the information-theoretic
  floor `k*(g) ≥ g² / E`, where `E` is the attention energy (collision
  probability).  The obvious question left open by cycle 2 — and recorded as the
  fifth direction of `FUTURE_DIRECTIONS.md` ("Flatness Dichotomy for the
  Cauchy–Schwarz Knee Floor") — is *how lossy* that floor is on a genuinely
  decaying row.  The conjecture recorded there was that on a geometric row
  `w i = (1 - a) aⁱ` the ratio

      (true knee) / (energy floor)

  **grows without bound** as `a → 1⁻`, since the true knee is logarithmic in
  `1/(1-g)` while the floor is `g²(1+a)/(1-a)`.

  This module settles it, and the recorded conjecture is **refuted**:

  * `geoRow_knee_le_log_bound`:  `k*(g) ≤ 1 + log(1/(1-g)) / (1-a)`;
  * `geoRow_knee_ge_floor`:      `g²(1+a)/(1-a) ≤ k*(g)`  (Cauchy–Schwarz, via
    the exact energy `E(a) = (1-a)/(1+a)`);
  * `geoRow_flatness_ratio_bounded` / `geoRow_ratio_blowup_refuted`: the two
    sides differ by at most the factor `(1 + log(1/(1-g)))/g²`, which depends on
    the gate **only** — uniformly in `a ∈ (0,1)`.  Both quantities diverge like
    `1/(1-a)`, so their ratio stays bounded and the floor is tight up to a
    gate-only constant.

  For the NET-63 gate `g = 0.98` the constant is explicit and small:
  `net63_flatness_constant_lt_six` shows six keys of slack suffice,
  `k* ≤ 6 · (g²/E)` for every geometric row.

  Consequences for the experimental thread.  The energy floor is *not* a weak
  bound that only bites on flat rows: on the entire geometric family it is
  within a factor `≈5` of the truth at gate `0.98`.  Hence a measured
  collision entropy really does predict the key budget up to a constant, which
  is what the deployment table needs; and the "flatness diagnostic" proposed in
  cycle 2 cannot be read off the ratio, because that ratio is bounded.

  All statements below are proved from scratch, with complete proofs.
-/


open Bridges.AttentionKneeFlatness

open Finset Bridges.AttentionKneeGeometry Bridges.AttentionKneeEntropyBound

/-! ## 1. The geometric attention row -/








/-! ## 2. The knee of a geometric row -/





/-! ## 3. The dichotomy: the floor is tight up to a gate-only constant -/

theorem Bridges.AttentionKneeFlatness.geoRow_ratio_blowup_refuted{g : ℝ} (hg0 : 0 < g) (hg1 : g < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℝ, 0 < a → a < 1 →
      (knee (geoRow a) g : ℝ) ≤ C * (g ^ 2 / geoEnergy a) := by sorry
