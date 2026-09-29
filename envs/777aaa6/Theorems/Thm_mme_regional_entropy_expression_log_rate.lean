-- Prove2me | Theorems.Thm_mme_regional_entropy_expression_log_rate
-- name    : mme_regional_entropy_expression_log_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T23:42:45.765542+00:00
-- url     : https://prove2.me/theorems/a4275195-730e-4d78-b21a-89bb6fb76992
-- title:
--   Asymptotic logarithmic rate of the complete regional entropy bound
-- statement:
--   For fixed tolerance and repair scale, uniformly replicate the regional sizes, split counts, and child profiles. The logarithm of the full entropy lower-bound expression, divided by the replication factor, tends to the original regional rate minus the original total size times the entropy modulus. The expression includes both polynomial denominator factors and the square-root progression loss. No positivity of the limiting rate is assumed.
-- source:
--   Asymptotic analysis of the exact expression used by IntegerStep.entropyLower in Def_mme_regional_entropy_copy_bound, under uniform replication of the regional profiles.

import Definitions.Def_mme_regional_entropy_copy_bound
import Theorems.Thm_mme_regional_mass_entropy_algebra
import Mathlib.Tactic.Ring
import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
open scoped Classical
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open MME.RegionRate
open BigOperators MME MME.RegionRate MME.RecursiveYZ
open Filter
set_option autoImplicit false
universe u

theorem mme_regional_entropy_expression_log_rate
    {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (eps : ℝ) (d : ℕ) :
    let size := fun k r => k * n r
    let counts := fun k r c => k * m r c
    let profiles := fun k i c w => k * mu i c w
    let E := fun k => regionalRate htotal (size k) (counts k) (profiles k)
    let loss := fun k => ((∑ r, size k r : ℕ) : ℝ) *
      entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) eps
    let theta := fun k => scaleExponent htotal (size k) (counts k) (profiles k) eps
    let factor := fun k => scaleFactor (half := half) (parent := parent) (size k) d ell
    Tendsto (fun k : ℕ =>
      Real.log (Real.exp (E k - loss k - 4 * Real.sqrt (Real.log (factor k) + theta k)) /
        (32 * polynomialFactor (size k) (Fintype.card (Cell half R parent)) * factor k)) /
          (k : ℝ)) atTop
      (nhds (regionalRate htotal n m mu - ((∑ r, n r : ℕ) : ℝ) *
        entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) eps)) := by sorry
