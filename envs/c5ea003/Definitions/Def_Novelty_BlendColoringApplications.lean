-- Prove2me | Definitions.Def_Novelty_BlendColoringApplications
-- name    : Novelty_BlendColoringApplications
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:08:03.919191+00:00
-- url     : https://prove2.me/theorems/83ecef61-a1e9-4f81-a3cf-1a460f221061
-- title:
--   Aether Catalog definitions — Novelty_BlendColoringApplications
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.BlendColoringApplications`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/BlendColoringApplications.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_BlendColoringHarmonic

/-!
# Applications of the blend-colouring collapse

This file specialises `Novelty.BlendColoringHarmonic.blend_const` to the two
statements the mission is really about:

* `no_nonconstant_blend`: the literal **non-existence** phrasing — a finite
  strongly connected row-stochastic digraph admits no blend colouring with two
  differently coloured vertices.
* the **directed `n`-cycle** (`n ≥ 1`): it is strongly connected, hence its only
  blend colourings are constant.

## Lab Notes

`-- !-- Lab Notes -- !--`

**Hypothesis.**  The maximum-principle collapse should specialise painlessly to
(a) the exact non-existence statement and (b) the canonical strongly connected
example, the directed cycle.

**Experiment.**  The `n`-cycle's arc relation is `j = i + 1` on `Fin n`; walking
`k` steps from `i` reaches `i + k`, and every vertex has the form `i + k`, giving
reachability.  Verified for `n = 2,3,4` by hand (see `ComputationalEvidence.md`).

**Analysis.**  Strong connectivity of the cycle is the only non-formal ingredient;
once established the collapse is immediate.  The internal `key` step of
`cycle_stronglyConnected` shows `i` reaches `i + m` for all `m`.

**Critique.**  Both results are non-vacuous: `no_nonconstant_blend` is applied to
the concrete cycle to rule out non-constant colourings, and the cycle is exhibited
as a genuine strongly connected witness (not the trivial one-vertex graph).

**Synthesis.**  The abstract theorem yields the headline non-existence result and
a concrete infinite family of instances.

`-- !-- Lab Notes -- !--`
-/

namespace Novelty.BlendColoringHarmonic

open scoped BigOperators
open Fin.NatCast


/-- Weight matrix of the directed `n`-cycle: the arc `i → i+1` has weight `1`. -/
def cycleWeight (n : ℕ) [NeZero n] : Fin n → Fin n → ℝ :=
  fun i j => if j = i + 1 then 1 else 0





end Novelty.BlendColoringHarmonic


