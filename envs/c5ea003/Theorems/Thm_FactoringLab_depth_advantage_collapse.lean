-- Prove2me | Theorems.Thm_FactoringLab_depth_advantage_collapse
-- name    : FactoringLab.depth_advantage_collapse
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:30:00.966389+00:00
-- url     : https://prove2.me/theorems/2456368c-8e92-4df0-ac71-1191044391ef
-- title:
--   Depth–advantage collapse.
-- statement:
--   **Depth–advantage collapse.**  Fix a palette `V`.  *Every* `N`-only adaptive
--   strategy whose outputs lie in `V` — of any size, any depth, any branching
--   pattern — obeys one and the same lower bound.  Enlarging the tree without
--   enlarging the palette cannot improve the prediction of the hidden factor.
--
--   ```lean
--   theorem FactoringLab.depth_advantage_collapse[DecidableEq κ] (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ)
--       (V : Finset ℝ) (hV : V.Nonempty) :
--       ∀ t : QTree ι, t.BandOnly Ω n → (∀ i ∈ Ω, t.eval i ∈ V) →
--         quantErr Ω n Y V hV + ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2
--           ≤ ∑ i ∈ Ω, (t.eval i - Y i) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/QuantizedBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/QuantizedBarrier.lean#L197

-- Thm stub generated from Probability/QuantizedBarrier.lean
import Mathlib
import Definitions.Def_Probability_AdaptiveBarrier
import Definitions.Def_Probability_QuantizedBarrier
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

open FactoringLab

variable {ι κ : Type*}

/-! ### Quantization error of the band means against a finite value set -/





/-! ### Adaptive strategies with finitely many output values -/


open QTree













/-! ### The depth–advantage collapse -/

theorem FactoringLab.depth_advantage_collapse[DecidableEq κ] (Ω : Finset ι) (n : ι → κ) (Y : ι → ℝ)
    (V : Finset ℝ) (hV : V.Nonempty) :
    ∀ t : QTree ι, t.BandOnly Ω n → (∀ i ∈ Ω, t.eval i ∈ V) →
      quantErr Ω n Y V hV + ∑ i ∈ Ω, (bandMean Ω n Y i - Y i) ^ 2
        ≤ ∑ i ∈ Ω, (t.eval i - Y i) ^ 2 := by sorry
