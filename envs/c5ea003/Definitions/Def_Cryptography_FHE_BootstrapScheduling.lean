-- Prove2me | Definitions.Def_Cryptography_FHE_BootstrapScheduling
-- name    : Cryptography_FHE_BootstrapScheduling
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T17:04:14.748108+00:00
-- url     : https://prove2.me/theorems/d8826681-184a-4e44-899e-7687cc926385
-- title:
--   Aether Catalog definitions — Cryptography_FHE_BootstrapScheduling
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.FHE.BootstrapScheduling`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/FHE/BootstrapScheduling.lean by skeleton subtraction
import Mathlib
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

namespace FHENoise

noncomputable section

/-! ## 1. Monotonicity of the noise iteration in the depth -/




/-! ## 2. Schedules -/

namespace Schedule

/-- The multiplicative depth realized by a schedule of block lengths. -/
def depth (sch : List ℕ) : ℕ := sch.sum

/-- The number of bootstraps performed by a schedule. -/
def bootstraps (sch : List ℕ) : ℕ := sch.length

/-- A schedule is *safe* for the parameters if every block, started from the
refreshed noise level `Bmin`, stays inside the decoding radius `T`. -/
def Safe (gamma D Bmin T : ℝ) (sch : List ℕ) : Prop :=
  ∀ n ∈ sch, iterD gamma D n Bmin ≤ T





end Schedule

end

end FHENoise


