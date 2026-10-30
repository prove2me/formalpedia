-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch8_Partitions_Erdos_umass_tendsto_zero
-- name    : AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_tendsto_zero
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-28T10:49:45.130243+00:00
-- url     : https://prove2.me/theorems/07dfdcac-9904-4744-ad3b-b9320e8e3bd9
-- title:
--   Conditional coalescence from energy drift and minorization
-- statement:
--   Conditional coalescence from a uniform positive off-Good energy drift and on-Good minorization; both quantitative hypotheses must be instantiated before use.
--
--   The full literal source contract is:
--
--   ```lean
--   theorem umass_tendsto_zero (D : α → α → ℝ) (c R δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
--       (hD : ∀ a b, (D a b) ^ 2 ≤ R ^ 2)
--       (hrow_off : ∀ x y, ¬ GoodW rnk W x y →
--           c ≤ (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) - (D x y) ^ 2)
--       (hminor : ∀ x y, GoodW rnk W x y → δ ≤ cmass P rnk W x y) :
--       Tendsto (umass P rnk W i j) atTop (𝓝 0)
--   ```
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch8/Partitions/UmassZero.lean#L41. Source code: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch8_Partitions_ITERCoupling
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# R7 Fact B via Doeblin: the unmatched mass tends to zero

Combining the D²-energy occupation control (`energy_controls_goodMass`) with the window-occupation bound
(`umass_le_one_sub_occupation`, giving `δ·∑goodMass ≤ 1`) shows the cumulative unmatched mass
`∑_{t<M} umass t ≤ K₀` is bounded uniformly in `M`.  Since `umass` is nonincreasing, `M·umass M ≤
∑_{t<M} umass t ≤ K₀`, so `umass M ≤ K₀/M → 0`.  This is the coalescence conclusion: the two coupled
killed chains' overlap → 1.  Deterministic finite-sum.  Opus-authored.
-/

open Finset Filter Topology

open AnalyticCombinatorics AnalyticCombinatorics.Ch8 AnalyticCombinatorics.Ch8.Partitions AnalyticCombinatorics.Ch8.Partitions.Erdos

variable {α : Type*} [Fintype α] [DecidableEq α]
variable (P : α → α → ℝ) (rnk : α → ℕ) (W : ℕ)
variable (hPnn : ∀ x y, 0 ≤ P x y) (hPmass : ∀ x, ∑ y, P x y = 1)
variable (i j : α)
include hPnn hPmass

theorem AnalyticCombinatorics.Ch8.Partitions.Erdos.umass_tendsto_zero (D : α → α → ℝ) (c R δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hD : ∀ a b, (D a b) ^ 2 ≤ R ^ 2)
    (hrow_off : ∀ x y, ¬ GoodW rnk W x y →
        c ≤ (∑ a, ∑ b, Kres P rnk W x y a b * (D a b) ^ 2) - (D x y) ^ 2)
    (hminor : ∀ x y, GoodW rnk W x y → δ ≤ cmass P rnk W x y) :
    Tendsto (umass P rnk W i j) atTop (𝓝 0) := by sorry
