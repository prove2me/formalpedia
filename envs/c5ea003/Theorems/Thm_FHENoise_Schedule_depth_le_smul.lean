-- Prove2me | Theorems.Thm_FHENoise_Schedule_depth_le_smul
-- name    : FHENoise.Schedule.depth_le_smul
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T20:47:58.908326+00:00
-- url     : https://prove2.me/theorems/d0fe75c7-ce4d-464e-803d-e00951188e4b
-- title:
--   Depth is bounded by blocks × bootstraps.
-- statement:
--   **Depth is bounded by blocks × bootstraps.**
--
--   ```lean
--   theorem FHENoise.Schedule.depth_le_smul{gamma D Bmin T : ℝ} (hg : 1 ≤ gamma) (hD : 0 ≤ D)
--       (hB : 1 ≤ Bmin) {L : ℕ} (hL : T < iterD gamma D (L + 1) Bmin)
--       {sch : List ℕ} (hsafe : Safe gamma D Bmin T sch) :
--       depth sch ≤ L * bootstraps sch := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FHE/BootstrapScheduling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FHE/BootstrapScheduling.lean#L91

-- Thm stub generated from Cryptography/FHE/BootstrapScheduling.lean
import Mathlib
import Definitions.Def_Cryptography_FHE_BootstrapScheduling
import Definitions.Def_Cryptography_FHE_Bootstrapping
import Definitions.Def_Cryptography_FHE_NoiseDichotomy

/-!
# Optimal bootstrap scheduling

`Cryptography.FHE.Bootstrapping` shows that refreshing every `L` levels succeeds
whenever `L` levels of noise growth stay under the decoding radius `T`.  This
file proves the matching *lower* bound: no schedule of bootstraps can do better.

A **schedule** is the list of block lengths between consecutive refreshes.  Its
total multiplicative depth is the sum of the list and its bootstrap count is the
length of the list.  Writing `L` for the largest safe block length, we prove:

* `Schedule.block_le_of_safe` — a correct schedule has every block of length
  `≤ L`, because the noise iteration is monotone in depth;
* `Schedule.depth_le_smul` — hence total depth `≤ L · (number of bootstraps)`;
* `Schedule.ceilDiv_le_bootstraps` — the number of bootstraps is at least
  `⌈d/L⌉`, matching the `⌈d/L⌉` refreshes used by `bootIter`;
* `Schedule.uniform_is_optimal` — the uniform schedule `replicate ⌈d/L⌉ L` is
  therefore an optimal bootstrap placement.

The monotonicity input (`iterD_mono_depth_of_one_le`) is where the mathematics
happens: for `γ ≥ 1`, `D ≥ 0` and a starting level `≥ 1` the quadratic noise map
is expanding, so longer blocks are strictly worse and greedy scheduling is
optimal.  Note the hypothesis `1 ≤ Bmin`: in normalized units this says that a
refreshed ciphertext still carries at least one unit of noise, which is exactly
what makes the refresh count nontrivial.
-/

open FHENoise

noncomputable section

/-! ## 1. Monotonicity of the noise iteration in the depth -/




/-! ## 2. Schedules -/

open Schedule

theorem FHENoise.Schedule.depth_le_smul{gamma D Bmin T : ℝ} (hg : 1 ≤ gamma) (hD : 0 ≤ D)
    (hB : 1 ≤ Bmin) {L : ℕ} (hL : T < iterD gamma D (L + 1) Bmin)
    {sch : List ℕ} (hsafe : Safe gamma D Bmin T sch) :
    depth sch ≤ L * bootstraps sch := by sorry
