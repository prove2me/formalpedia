-- Prove2me | solution 1 for Catalog.Novelty.AttentionScaleThreshold.exists_multiple_between
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T17:55:18.794848+00:00
-- url     : https://prove2.me/submissions/5b57de8d-db35-4e1f-bb37-8a19a0dd62fb

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






/-! ### 3. The scale exponent and the context-free threshold -/


















open Catalog.Novelty.AttentionScaleThreshold in
theorem solution(d n : ℕ) (hd : 0 < d) :
    ∃ k, d ∣ k ∧ n ≤ k ∧ k < n + d := by
  have hne : {m : ℕ | n ≤ d * m}.Nonempty := ⟨n, Nat.le_mul_of_pos_left n hd⟩
  have hmem : n ≤ d * sInf {m : ℕ | n ≤ d * m} := Nat.sInf_mem hne
  refine ⟨d * sInf {m : ℕ | n ≤ d * m}, ⟨_, rfl⟩, hmem, ?_⟩
  rcases Nat.eq_zero_or_pos (sInf {m : ℕ | n ≤ d * m}) with h | h
  · rw [h] at hmem ⊢
    simp only [Nat.mul_zero] at hmem ⊢
    omega
  · obtain ⟨m', hm'⟩ := Nat.exists_eq_succ_of_ne_zero h.ne'
    have hlt : d * m' < n := by
      by_contra hle
      have hmem' : m' ∈ {m : ℕ | n ≤ d * m} := not_lt.mp hle
      have := Nat.sInf_le hmem'
      omega
    calc d * sInf {m : ℕ | n ≤ d * m} = d * m' + d := by
          rw [hm', Nat.succ_eq_add_one]; ring
      _ < n + d := by omega
