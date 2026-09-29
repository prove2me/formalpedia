-- Prove2me | solution 1 for AttentionMarginLaw.margin_depth_independent
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T00:42:09.895554+00:00
-- url     : https://prove2.me/submissions/65cd27de-3a64-480c-b9a1-a51b8bd4c0b1

-- Sol generated from Probability/AttentionMarginLaw.lean
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






/-!
## 4.  The margin is pinned too: the knee window, and depth-independence

The two-sided margin law has a dimensionless reading.  Write
`x = 4·L·B·A·ctx/m` for the real budget the margin channel asks for.  Then the
integer knee always sits in the closed window `[x, 2x]`, so the dimensionless
number `k*·m/(4·L·B·A·ctx)` is confined to `[1, 2]` — a window fixed before any
measurement, with no free constant to fit.  And if the measured depth-linear
knee is what the margin channel selects, the margin itself is forced:
`m = 128·L·B·A` at *every* depth.
-/


/-- **The margin is forced by the depth-linear knee.**  If the budget the margin
channel asks for equals the measured `d·ctx/32` at some depth `d`, then
`m = 128·L·B·A` — a value with no `d` in it. -/
theorem margin_forced_by_depth_linear_knee {A ctx L B m : ℝ} {d : ℕ} (hd : 0 < d)
    (hctx : 0 < ctx) (hm : 0 < m)
    (hlaw : 4 * L * B * A * d * ctx / m = d * ctx / 32) :
    m = 128 * L * B * A := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h1 : 4 * L * B * A * d * ctx = ((d : ℝ) * ctx / 32) * m :=
    (div_eq_iff hm.ne').mp hlaw
  have hne : ((d : ℝ) * ctx) ≠ 0 := by positivity
  have hcancel : (128 * L * B * A) * ((d : ℝ) * ctx) = m * ((d : ℝ) * ctx) := by
    linear_combination 32 * h1
  exact (mul_right_cancel₀ hne hcancel).symm



open AttentionMarginLaw in
theorem solution{A ctx L B m₄ m₁₆ : ℝ} (hctx : 0 < ctx)
    (hm₄ : 0 < m₄) (hm₁₆ : 0 < m₁₆)
    (h4 : 4 * L * B * A * 4 * ctx / m₄ = 4 * ctx / 32)
    (h16 : 4 * L * B * A * 16 * ctx / m₁₆ = 16 * ctx / 32) :
    m₄ = m₁₆ ∧ m₁₆ ≠ m₄ / 4 := by
  have e4 : m₄ = 128 * L * B * A :=
    margin_forced_by_depth_linear_knee (d := 4) (by norm_num) hctx hm₄
      (by push_cast; linarith [h4])
  have e16 : m₁₆ = 128 * L * B * A :=
    margin_forced_by_depth_linear_knee (d := 16) (by norm_num) hctx hm₁₆
      (by push_cast; linarith [h16])
  refine ⟨by rw [e4, e16], ?_⟩
  intro hcon
  rw [e4, e16] at hcon
  have : (0 : ℝ) < 128 * L * B * A := by rw [← e4]; exact hm₄
  linarith
