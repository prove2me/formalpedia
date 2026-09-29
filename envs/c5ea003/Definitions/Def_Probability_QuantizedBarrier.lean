-- Prove2me | Definitions.Def_Probability_QuantizedBarrier
-- name    : Probability_QuantizedBarrier
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:35:48.09871+00:00
-- url     : https://prove2.me/theorems/1f86f393-9c36-46dc-960d-dfc6ec60cdc5
-- title:
--   Aether Catalog definitions — Probability_QuantizedBarrier
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.QuantizedBarrier`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/QuantizedBarrier.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_AdaptiveBarrier
import Definitions.Def_Probability_StructuralOrthogonality
/-
# The quantized (depth–advantage collapse) barrier
(Factoring Lab, Phase A v19c — cycle 3)

This file closes next-cycle sub-conjecture 1 of `FUTURE_DIRECTIONS.md`: for an
`N`-only adaptive strategy the *only* thing that matters is the set of values it
can output, not the depth or the branching structure of the search that produces
them.

`Catalog/Probability/AdaptiveBarrier.lean` shows that no `N`-only decision tree
beats the band mean.  That bound is uniform but not quantitative: it does not
say how far from the band mean a *small* strategy must be.  Here we sharpen it.
A strategy that can emit only the finitely many values `V` incurs, on top of the
irreducible band-conditional error, the **quantization error** of the band means
against `V`:

`Σ_{i∈Ω} min_{v ∈ V} (v − E[Y | n(i)])²`   (`FactoringLab.quantErr`).

The results are:

* `FactoringLab.quantized_barrier` — every `N`-only predictor with values in `V`
  has squared error at least `quantErr(V) + (band-conditional error)`;
* `FactoringLab.QTree` — adaptive strategies with *constant* leaves, together
  with `FactoringLab.QTree.card_vals_le_size_succ` (`|V| ≤ size + 1`) and
  `FactoringLab.QTree.eval_mem_vals`;
* `FactoringLab.qtree_quantized_barrier` — the barrier for such a strategy,
  and `FactoringLab.depth_advantage_collapse`: among all `N`-only strategies
  emitting values in a fixed set `V`, *every* one is stuck at the same lower
  bound, whatever its size; so growing the tree past the point where its `|V|`
  values are realized buys nothing;
* `FactoringLab.quantErr_pos` — the bound has real content: as soon as one band
  mean is missed by `V`, the quantization error is strictly positive, so a
  `k`-valued strategy is *strictly* worse than the band mean;
* `FactoringLab.QTree.toDTree_eval` and `FactoringLab.QTree.bandOnly_toDTree` —
  constant-leaf strategies are genuine decision trees in the sense of
  `AdaptiveBarrier.lean`, so the two barriers compose.
-/

open Finset

namespace FactoringLab

variable {ι κ : Type*}

/-! ### Quantization error of the band means against a finite value set -/

/-- The **quantization error**: the total squared distance from the band means
to the nearest available output value.  This is the price a strategy pays for
being able to emit only finitely many values. -/
noncomputable def quantErr [DecidableEq κ] (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ)
    (V : Finset ℝ) (hV : V.Nonempty) : ℝ :=
  ∑ i ∈ Ω, V.inf' hV fun v => (v - bandMean Ω n Y i) ^ 2




/-! ### Adaptive strategies with finitely many output values -/

/-- A finite adaptive strategy with *constant* leaves: the outputs form a finite
palette, whose size is what the barrier below charges for. -/
inductive QTree (ι : Type*) where
  | leaf (v : ℝ) : QTree ι
  | node (test : ι → Bool) (l r : QTree ι) : QTree ι

namespace QTree

/-- Running the strategy. -/
def eval : QTree ι → ι → ℝ
  | leaf v, _ => v
  | node t l r, i => if t i then eval l i else eval r i

/-- Number of internal tests. -/
def size : QTree ι → ℕ
  | leaf _ => 0
  | node _ l r => l.size + r.size + 1

/-- The palette: the finite set of values the strategy can emit. -/
noncomputable def vals : QTree ι → Finset ℝ
  | leaf v => {v}
  | node _ l r => l.vals ∪ r.vals

/-- Band-measurability of all the tests (the leaves are constants, hence
automatically band-measurable). -/
def BandOnly (Ω : Finset ι) (n : ι → κ) : QTree ι → Prop
  | leaf _ => True
  | node t l r => BandMeasurable Ω n t ∧ BandOnly Ω n l ∧ BandOnly Ω n r




/-- Constant-leaf strategies are decision trees in the sense of
`AdaptiveBarrier.lean`. -/
def toDTree : QTree ι → DTree ι
  | leaf v => DTree.leaf (fun _ => v)
  | node t l r => DTree.node t l.toDTree r.toDTree




end QTree

/-! ### The depth–advantage collapse -/




end FactoringLab


