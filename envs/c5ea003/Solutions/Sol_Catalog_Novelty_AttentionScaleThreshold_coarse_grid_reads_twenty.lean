-- Prove2me | solution 1 for Catalog.Novelty.AttentionScaleThreshold.coarse_grid_reads_twenty
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:55:18.074832+00:00
-- url     : https://prove2.me/submissions/f266b262-b0ee-44c0-9d55-7bcabd24bd4a

-- Sol generated from Novelty/AttentionScaleThreshold.lean
import Mathlib
import Definitions.Def_Novelty_AttentionRetentionKnee
import Definitions.Def_Novelty_AttentionScaleThreshold

/-!
# Hinges, grid resolution, and the scale threshold (NET-67, cycle 2)

This is the second research cycle on the NET-67 measurement.  Cycle 1
(`Novelty.AttentionBudgetIncrement`, `Novelty.AttentionRetentionKnee`) fixed the
two measured budget laws, audited the verdict, and derived the additive law from
a decay rate degrading like `1/log(context)`.  Three questions were left open,
and each gets a theorem here.

**(1) How much does the measured triple actually determine?**  The 1.5B curve is
a *hinge* `max 16 (base + slope·j)`.  `hingeFits_iff` characterises all hinges
through the measured points `16, 16, 18`, and the answer is uncomfortable:
`hingeFits_slope_ge_two` shows the data only force `slope ≥ 2`, and
`hingeFits_alternative` exhibits a genuinely different fit (`base = 12`,
`slope = 3`).  So the advertised `+2` is a **lower bound**, not a measurement.
`hinge_prediction_discriminates` shows the two fits separate at the very next
octave (`20` versus `21` keys at `4096`), which is exactly the experiment to run.

**(2) Why did NET-66 read `20` where NET-67 reads `18`?**  Because a knee read
on a coarse grid is the least *grid point* above the true knee.  `kneeMul` is
the grid-restricted knee and `kneeMul_bounds` proves the two-sided estimate
`knee ≤ kneeMul < knee + d`.  `coarse_grid_reads_twenty` realises the NET-66/67
discrepancy exactly: a profile whose true knee is `18` is read as `20` on the
spacing-`4` grid, and the error is provably below the spacing.

**(3) Does the halving extrapolate to 7B?**  Cycle 1 calibrated the peakedness
of the two models to `λ₀ = 1` and `λ₀ = 2` at parameter counts `0.5B` and
`1.5B`, i.e. `λ₀(N) = (2N)^θ` with `θ = log 2 / log 3`.  The induced increment
law `incrAt N = 4·(2N)^(-θ)` reproduces both measurements
(`incrAt_half`, `incrAt_three_halves`), is strictly decreasing
(`incrAt_strictAntiOn`), and has an **exact closed-form threshold**:
`incrAt N < 1 ↔ 4.5 < N` (`incrAt_lt_one_iff`).  Hence
`scale_threshold_four_point_five`: *a model above 4.5B parameters needs less
than one extra key per context doubling* — its attention budget is essentially
context-free.  For the proposed 7B cell the prediction is bracketed exactly:
`1/2 < incrAt 7 < 1` (`prediction_7B`).
-/

open Catalog.Novelty.AttentionScaleThreshold

open Catalog.Novelty.AttentionBudgetIncrement Catalog.Novelty.AttentionRetentionKnee

/-! ### 1. Hinges: what the measured triple does and does not determine -/












/-! ### 2. Grid resolution: why a coarse sweep over-reads the knee -/




/-- The flat profile: every key carries weight `1`, so `retained k = k`.
It is the cleanest test object for a knee measurement. -/
theorem retained_one (k : ℕ) : retained (fun _ => (1 : ℝ)) k = k := by
  simp [retained]


/-! ### 3. The scale exponent and the context-free threshold -/


















open Catalog.Novelty.AttentionScaleThreshold in
theorem solution:
    knee (fun _ => (1 : ℝ)) 18 = 18 ∧ kneeMul (fun _ => (1 : ℝ)) 18 4 = 20 := by
  have hset : {k : ℕ | (18 : ℝ) ≤ retained (fun _ => (1 : ℝ)) k} = {k : ℕ | 18 ≤ k} := by
    ext k
    simp [retained_one, Nat.ofNat_le_cast]
  have hset' : {k : ℕ | 4 ∣ k ∧ (18 : ℝ) ≤ retained (fun _ => (1 : ℝ)) k}
      = {k : ℕ | 4 ∣ k ∧ 18 ≤ k} := by
    ext k
    simp [retained_one, Nat.ofNat_le_cast]
  constructor
  · rw [knee, hset]
    apply le_antisymm
    · exact Nat.sInf_le (by simp)
    · exact le_csInf ⟨18, by simp⟩ fun b hb => hb
  · rw [kneeMul, hset']
    apply le_antisymm
    · exact Nat.sInf_le ⟨by norm_num, by norm_num⟩
    · refine le_csInf ⟨20, ⟨by norm_num, by norm_num⟩⟩ ?_
      rintro b ⟨hdvd, hb⟩
      obtain ⟨c, rfl⟩ := hdvd
      omega
