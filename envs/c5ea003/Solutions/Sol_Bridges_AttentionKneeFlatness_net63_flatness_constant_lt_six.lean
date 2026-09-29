-- Prove2me | solution 1 for Bridges.AttentionKneeFlatness.net63_flatness_constant_lt_six
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:15:59.674199+00:00
-- url     : https://prove2.me/submissions/d8d69b78-3fb5-45b5-b100-726f8904541a

-- Sol generated from Bridges/AttentionKneeFlatness.lean
import Mathlib
import Definitions.Def_Bridges_AttentionKneeEntropyBound
import Definitions.Def_Bridges_AttentionKneeFlatness
import Definitions.Def_Bridges_AttentionKneeGeometry
import Theorems.Thm_Bridges_AttentionKneeFlatness_geoRow_flatness_ratio_bounded
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






lemma geoEnergy_pos {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) : 0 < geoEnergy a := by
  unfold geoEnergy
  apply div_pos <;> linarith


/-! ## 2. The knee of a geometric row -/





/-! ## 3. The dichotomy: the floor is tight up to a gate-only constant -/




/-! ## 4. The NET-63 gate: an explicit small constant -/

lemma log_fifty_lt_four : Real.log 50 < 4 := by
  have he : (50:ℝ) < Real.exp 4 := by
    have h1 : (2.7182818283:ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h4 : Real.exp 4 = (Real.exp 1) ^ 4 := by
      rw [← Real.exp_nat_mul]; norm_num
    have hpos : (0:ℝ) < Real.exp 1 := Real.exp_pos 1
    rw [h4]
    nlinarith [pow_pos hpos 2, pow_pos hpos 3]
  have := Real.log_lt_log (by norm_num) he
  rwa [Real.log_exp] at this



/-!
## Lab Notes (cycle 3)

* Recorded conjecture (FUTURE_DIRECTIONS, direction 5): on geometric rows the
  ratio `(true knee)/(g²/E)` "grows without bound as `a → 1`".
  **Refuted** (`geoRow_ratio_blowup_refuted`): the ratio is bounded by
  `(1 + log(1/(1-g)))/g²`, a function of the gate alone.  The source of the
  error is that both quantities diverge at the same rate `1/(1-a)`:
  `k* ≈ log(1/(1-g))/(1-a)` and `g²/E = g²(1+a)/(1-a)`.
* Numerical check at the NET-63 gate `g = 0.98`:
  `log(1/(0.02)) = log 50 ≈ 3.912`, constant `(1+3.912)/0.9604 ≈ 5.11 < 6`
  (`net63_flatness_constant_lt_six`, using `log 50 < 4`).
* Dyadic instance `a = 1/2`: `E = 1/3`, floor `= 2.8812`, true knee `= 6`
  (`dyadic_knee_and_floor`), ratio `2.08` — consistent with the bound and with
  the cycle-1 computation `knee geometricProfile 0.98 = 6`.
-/


open Bridges.AttentionKneeFlatness in
theorem solution{a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    (knee (geoRow a) 0.98 : ℝ) ≤ 6 * ((0.98:ℝ) ^ 2 / geoEnergy a) := by
  have hfloor_pos : (0:ℝ) < (0.98:ℝ) ^ 2 / geoEnergy a := by
    have := geoEnergy_pos (le_of_lt ha0) ha1
    positivity
  have hmain := geoRow_flatness_ratio_bounded (g := (0.98:ℝ)) ha0 ha1 (by norm_num) (by norm_num)
  have hlog : Real.log ((1:ℝ) - 0.98)⁻¹ < 4 := by
    have h50 : ((1:ℝ) - 0.98)⁻¹ = 50 := by norm_num
    rw [h50]; exact log_fifty_lt_four
  have hconst : (1 + Real.log ((1:ℝ) - 0.98)⁻¹) / (0.98:ℝ) ^ 2 ≤ 6 := by
    rw [div_le_iff₀ (by norm_num)]
    nlinarith
  calc (knee (geoRow a) 0.98 : ℝ)
      ≤ ((1 + Real.log ((1:ℝ) - 0.98)⁻¹) / (0.98:ℝ) ^ 2) * ((0.98:ℝ) ^ 2 / geoEnergy a) := hmain
    _ ≤ 6 * ((0.98:ℝ) ^ 2 / geoEnergy a) :=
        mul_le_mul_of_nonneg_right hconst (le_of_lt hfloor_pos)
