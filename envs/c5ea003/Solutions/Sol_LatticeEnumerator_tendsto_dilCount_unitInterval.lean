-- Prove2me | solution 1 for LatticeEnumerator.tendsto_dilCount_unitInterval
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:09:07.457581+00:00
-- url     : https://prove2.me/submissions/47d53f87-1290-4405-8b78-2495f082a628

-- Sol generated from Cryptography/LatticePointExamples.lean
import Mathlib
import Definitions.Def_Cryptography_LatticePointEnumerator
import Definitions.Def_Cryptography_LatticePointUniqueness
import Theorems.Thm_LatticeEnumerator_dilCount_unitInterval

/-!
# Worked examples and computational sanity checks

Concrete evaluations of the lattice-point enumerator, used as machine-checked evidence that the
definitions in `Cryptography.LatticePointEnumerator` behave as intended.

## Main results

* `LatticeEnumerator.dilCount_unitInterval` : in dimension one, `L_{[0,1)}(t) = ⌈t⌉` for every
  `t > 0`; in particular `L(t)/t → 1 = vol([0,1))`, in agreement with the Gauss–Weyl theorem.
* `LatticeEnumerator.dilCount_unitInterval_examples` : numerical instances.
* `LatticeEnumerator.dilCount_empty`, `LatticeEnumerator.shiftCount_empty` : degenerate cases.
-/

noncomputable section

open MeasureTheory Metric Set Filter Topology

open LatticeEnumerator







open LatticeEnumerator in
theorem solution:
    Tendsto (fun t : ℝ => (dilCount (Set.univ.pi fun _ : Fin 1 => Set.Ico (0 : ℝ) 1) t : ℝ) / t)
      atTop (𝓝 1) := by
  have hsq : ∀ t : ℝ, 0 < t →
      (dilCount (Set.univ.pi fun _ : Fin 1 => Set.Ico (0 : ℝ) 1) t : ℝ) / t ≤ 1 + 1 / t := by
    intro t ht
    rw [dilCount_unitInterval ht, div_le_iff₀ ht]
    have h1 : ((⌈t⌉₊ : ℕ) : ℝ) < t + 1 := Nat.ceil_lt_add_one ht.le
    have h2 : (1 + 1 / t) * t = t + 1 := by field_simp
    rw [h2]
    exact h1.le
  have hsq' : ∀ t : ℝ, 0 < t →
      (1 : ℝ) ≤ (dilCount (Set.univ.pi fun _ : Fin 1 => Set.Ico (0 : ℝ) 1) t : ℝ) / t := by
    intro t ht
    rw [dilCount_unitInterval ht, le_div_iff₀ ht, one_mul]
    exact Nat.le_ceil t
  have hupper : Tendsto (fun t : ℝ => 1 + 1 / t) atTop (𝓝 1) := by
    have : Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) := by
      simpa [one_div] using tendsto_inv_atTop_zero
    simpa using tendsto_const_nhds.add this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht using hsq' t ht
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht using hsq t ht
