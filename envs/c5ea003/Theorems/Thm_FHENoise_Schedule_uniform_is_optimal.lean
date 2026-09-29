-- Prove2me | Theorems.Thm_FHENoise_Schedule_uniform_is_optimal
-- name    : FHENoise.Schedule.uniform_is_optimal
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T20:49:00.825777+00:00
-- url     : https://prove2.me/theorems/30d7c241-f02b-41bb-92d3-6b6601303e9d
-- title:
--   Optimality of the uniform schedule.
-- statement:
--   **Optimality of the uniform schedule.**  For any target depth `d`, the
--   schedule consisting of `⌈d/L⌉` blocks of `L` levels is safe, reaches depth at
--   least `d`, and uses exactly the minimum possible number of bootstraps.
--
--   ```lean
--   theorem FHENoise.Schedule.uniform_is_optimal{gamma D Bmin T : ℝ} (hg : 1 ≤ gamma) (hD : 0 ≤ D)
--       (hB : 1 ≤ Bmin) {L : ℕ} (hLpos : 0 < L) (hL : T < iterD gamma D (L + 1) Bmin)
--       (hsafeL : iterD gamma D L Bmin ≤ T) (d : ℕ) :
--       Safe gamma D Bmin T (List.replicate (d ⌈/⌉ L) L) ∧
--         d ≤ depth (List.replicate (d ⌈/⌉ L) L) ∧
--         bootstraps (List.replicate (d ⌈/⌉ L) L) = d ⌈/⌉ L ∧
--         (∀ sch : List ℕ, Safe gamma D Bmin T sch → d ≤ depth sch →
--           bootstraps (List.replicate (d ⌈/⌉ L) L) ≤ bootstraps sch) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/FHE/BootstrapScheduling.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/FHE/BootstrapScheduling.lean#L108

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

theorem FHENoise.Schedule.uniform_is_optimal{gamma D Bmin T : ℝ} (hg : 1 ≤ gamma) (hD : 0 ≤ D)
    (hB : 1 ≤ Bmin) {L : ℕ} (hLpos : 0 < L) (hL : T < iterD gamma D (L + 1) Bmin)
    (hsafeL : iterD gamma D L Bmin ≤ T) (d : ℕ) :
    Safe gamma D Bmin T (List.replicate (d ⌈/⌉ L) L) ∧
      d ≤ depth (List.replicate (d ⌈/⌉ L) L) ∧
      bootstraps (List.replicate (d ⌈/⌉ L) L) = d ⌈/⌉ L ∧
      (∀ sch : List ℕ, Safe gamma D Bmin T sch → d ≤ depth sch →
        bootstraps (List.replicate (d ⌈/⌉ L) L) ≤ bootstraps sch) := by sorry
