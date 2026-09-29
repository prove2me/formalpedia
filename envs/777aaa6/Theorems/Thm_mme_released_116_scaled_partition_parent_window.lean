-- Prove2me | Theorems.Thm_mme_released_116_scaled_partition_parent_window
-- name    : mme_released_116_scaled_partition_parent_window
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:33:28.818251+00:00
-- url     : https://prove2.me/theorems/a9d09df4-01f2-401d-a06a-aa437580523b
-- title:
--   Every positive scaled (1,1,6) regional window lies in the released global window
-- statement:
--   For each positive integer $k$, the $kd^4$ physical parent positions of the released owner-zero $(1,1,6)$ component admit a partition into six regions of sizes $kn_r$. In each mode, typicality of all regional pair-word histograms with the scaled integer profiles implies
--   $$\left|\frac{\#\{p:f(p)=w\}}{kd^4}-\frac{H_i(w)}{d^4}\right|\le\varepsilon$$
--   for every full word $w$, where $H_i$ is the exact released joint-row marginal. The center is independent of $k$. This is physical histogram-window inclusion at all positive integer scales; extraction rates remain separate requirements.
-- source:
--   Integer replication of regional profiles and the released owner-zero (1,1,6) component.

import Theorems.Thm_mme_released_116_weighted_parent_center
import Definitions.Def_mme_released_116_integer_profiles
import Definitions.Def_mme_complete_split_concatenation
import Mathlib.Data.Fintype.EquivFin
import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Fin.Basic

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false


open MME.Released116 MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_116_scaled_partition_parent_window (k : ℕ) (hk : 0 < k) :
    ∃ positions : (Σ r : Fin 6, Fin (k * regionalSize r)) ≃
        Fin (k * denominator ^ 4),
      ∀ (i : Fin 3) (f : Fin (k * denominator ^ 4) → CompleteWord 3) (eps : ℝ),
        parentTypical parent_total (fun r => k * regionalSize r)
          (fun r c => k * splitCount r c) (fun c w => k * integerProfile i c w) eps
          (fun p =>
            let v := (completeWordSplitEquiv 2 (by decide)) (f (positions ⟨p.1,p.2.1⟩))
            ![v.1,v.2] p.2.2) →
        ∀ w : CompleteWord 3,
          |(Fintype.card {p : Fin (k * denominator ^ 4) // f p = w} : ℝ) /
              (k * denominator ^ 4 : ℕ) -
            ((((ReleasedGlobal.jointRows 0 10).map
              (fun p => if ReleasedGlobal.atom p.1 i = w then p.2 else 0)).sum : ℕ) : ℝ) /
              (denominator : ℝ) ^ 4| ≤ eps := by sorry
