-- Prove2me | Theorems.Thm_SpecDecCPU_genSpeedup_succ_lt_iff
-- name    : SpecDecCPU.genSpeedup_succ_lt_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:26:38.530992+00:00
-- url     : https://prove2.me/theorems/5ca3c4bc-0391-4301-9a67-940d1e01d7ec
-- title:
--   Gen speedup succ lt iff
-- statement:
--   Formal statement of `SpecDecCPU.genSpeedup_succ_lt_iff` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem SpecDecCPU.genSpeedup_succ_lt_iff{Y : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (d : ℕ) :
--       genSpeedup Y c (d + 1) < genSpeedup Y c d ↔
--         (Y (d + 1) - Y d) * blockCost c d < c * Y d := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/SpeculativeDecodingDepthUnimodality.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/SpeculativeDecodingDepthUnimodality.lean#L72

-- Thm stub generated from Shared/SpeculativeDecodingDepthUnimodality.lean
import Mathlib
import Definitions.Def_Shared_SpeculativeDecodingCostDominance
import Definitions.Def_Shared_SpeculativeDecodingDepthUnimodality

/-!
# Unimodality of throughput in draft depth, and the validity of greedy depth tuning

Cycle 2 of the NET-91 thread.  Cycle 1
(`Shared.SpeculativeDecodingCostDominance`) established *draft-cost dominance* and the
fact that the "deepening pays" frontier is monotone in acceptance.  It left open the
question a practitioner actually faces: the experiment tuned depth on the grid
`{2, 4, 8}` and found different winners per domain — but is a *local* search over depth
guaranteed to find the *global* optimum, or can throughput have several humps, so that
the observed prose collapse past `d = 4` hides a later revival?

The answer here is a genuine structure theorem: **for any yield with nonincreasing
increments over an affine cost, throughput in depth is unimodal**.  Once one extra draft
step fails to pay, no deeper step ever pays again (`decline_propagates`,
`decline_persists`), so hill-climbing from `d = 0` and stopping at the first
non-improving step returns a global optimum (`greedy_depth_optimal`).  Concavity of the
yield is exactly what the i.i.d. model supplies — its increments are `a ^ (d+1)` — and it
is also the qualitative property any position-dependent acceptance profile with
nonincreasing per-position acceptance enjoys.  So the *grid* `{2, 4, 8}` used in NET-91
cannot have missed a second hump: the measured collapse is terminal.

Instantiated at the measured 0.5B-draft cost `c = 0.118`, the model's optimal depths are

  prose (`a = 0.477`) : `d* = 2`   (`prose_optimal_depth_two`)
  code  (`a = 0.630`) : `d* = 3`   (`code_optimal_depth_three`)

a strict, provable domain split (`optimal_depth_domain_split`): at exactly the same
depth-3 decision the two domains disagree, so no single static depth is optimal for both.

-- !-- Lab Notes -- !--
Hypothesizer (cycle 2, 5 conjectures):
 (C1) [BOLD] Throughput is unimodal in depth for every concave yield: the depth landscape
      has no second hump, so greedy tuning is exact.
 (C2) The i.i.d. yield is concave, hence C1 applies to cycle 1's model verbatim.
 (C3) The model's optimal depths for the measured prose and code acceptances differ, and
      the difference is exhibited by a single decision (`d = 2 → 3`).
 (C4) Concavity is *necessary* in the sense that an affine yield (cycle 1's mean-yield
      reading) has no interior optimum at all — already proved in cycle 1.
 (C5) Unimodality plus cycle 1's monotone frontier gives a monotone optimal-depth
      selector: higher acceptance never lowers the greedy stopping depth.

Experimenter: C1–C3 and C5 are formalised below with zero sorries; C4 is
`SpecDecCPU.affine_ratio_mono` / `affine_ratio_anti` from cycle 1.

Analyst: the proof of C1 is a two-line marginal-cost computation once the comparison is
put in cross-multiplied form: `speedup (d+1) < speedup d` is *equivalent* to
`increment d * blockCost c d < c * yield d`, and the left side is nonincreasing while the
right side is nondecreasing in `d`.  The same identity explains why the affine reading has
no interior optimum: there the two sides are, respectively, constant and affine, so they
cross at most once and never re-cross.

Critic: the two numeric optima are corollaries of the general theorem, not standalone
`norm_num` facts — each needs three evaluated comparisons plus `greedy_depth_optimal` to
become a statement quantified over *all* depths.
-/

open SpecDecCPU

open Finset

/-! ## A general concave-yield block model -/

theorem SpecDecCPU.genSpeedup_succ_lt_iff{Y : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (d : ℕ) :
    genSpeedup Y c (d + 1) < genSpeedup Y c d ↔
      (Y (d + 1) - Y d) * blockCost c d < c * Y d := by sorry
