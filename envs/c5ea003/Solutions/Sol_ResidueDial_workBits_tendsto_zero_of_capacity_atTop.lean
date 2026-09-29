-- Prove2me | solution 1 for ResidueDial.workBits_tendsto_zero_of_capacity_atTop
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:59:22.053399+00:00
-- url     : https://prove2.me/submissions/6bb0d53c-f1e1-475e-b497-031d618f3f59

-- Sol generated from Cryptography/ResidueDial/Battery.lean
import Mathlib
import Definitions.Def_Cryptography_ResidueDial_Battery
import Definitions.Def_Cryptography_ResidueDial_Core
import Theorems.Thm_ResidueDial_dialCost_ne_zero
import Theorems.Thm_ResidueDial_speedup_of_trivial

/-!
# Batteries of residue dials: CRT composition and the bit-currency separation

A *battery* is a family of residue dials on pairwise coprime moduli, read
simultaneously.  The Chinese Remainder Theorem says that the joint filter on the
product modulus is exactly the "AND" of the individual filters
(`mem_crtDial`), and that its density is the *product* of the individual
densities (`crtDial_density`).

Two consequences are proved here.

* **The battery cap is still `4/3`** (`crtDial_speedup_le_four_thirds`,
  `batteryDensity_speedup_le_four_thirds`): composing dials — any number of
  them, on any moduli — cannot beat a single dial.  Composition is *free* in the
  sense that it costs nothing and buys nothing beyond the universal cap.

* **Capacity bits and work bits are different currencies.**  A battery of `n`
  half-density dials advertises `n` bits of capacity
  (`capacityBits_half_pow`), yet the work it buys is
  `workBits ≤ logb 2 (4/3) < 1` bit (`workBits_le_cap`, `workBits_lt_one`),
  and in fact tends to `0` as the capacity grows
  (`workBits_tendsto_zero_of_capacity_atTop`).  So the measured "battery bits"
  of a residue battery cannot be converted into work bits at par: capacity is
  unbounded while work is capped at `logb 2 (4/3)`.
-/

open ResidueDial

open Finset

/-! ## CRT composition of two dials -/







/-! ## Batteries of arbitrarily many dials -/









/-! ## Capacity bits versus work bits -/








/-- `speedup` is continuous wherever it is defined — the cost never vanishes. -/
theorem continuous_speedup : Continuous speedup := by
  unfold speedup dialCost
  apply Continuous.div continuous_const (by continuity)
  intro x
  simpa [dialCost] using dialCost_ne_zero x



open ResidueDial in
theorem solution:
    Filter.Tendsto (fun n : ℕ => workBits ((1 / 2 : ℝ) ^ n)) Filter.atTop (nhds 0) := by
  have hθ : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hs : Filter.Tendsto (fun n : ℕ => speedup ((1 / 2 : ℝ) ^ n)) Filter.atTop (nhds 1) := by
    have hcont : Filter.Tendsto speedup (nhds 0) (nhds (speedup 0)) :=
      continuous_speedup.tendsto 0
    have hcomp := hcont.comp hθ
    rwa [speedup_of_trivial (Or.inl rfl)] at hcomp
  have hlog : Filter.Tendsto (fun x : ℝ => Real.logb 2 x) (nhds 1) (nhds 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ => Real.logb 2 x) (nhds 1) (nhds (Real.logb 2 1)) :=
      Real.continuousAt_logb (b := 2) (by norm_num)
    rwa [Real.logb_one] at h1
  exact hlog.comp hs
