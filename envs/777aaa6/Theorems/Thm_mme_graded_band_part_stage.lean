-- Prove2me | Theorems.Thm_mme_graded_band_part_stage
-- name    : mme_graded_band_part_stage
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T16:52:39.716966+00:00
-- url     : https://prove2.me/theorems/5d673b53-781e-4970-a100-af61d306eba4
-- title:
--   Graded part stage over histogram types in a band
-- statement:
--   This result builds a graded part stage whose steps are indexed by histogram types.
--
--   Fix regional data at level `ell` as in the band step certified rate, and take `0 <= c` below the regional rate. Then there is `eta > 0` with the following property, for all large scales `t`.
--
--   Take any target address `a` and any per-mode condition `good` on histograms. Every histogram satisfying `good` must have the scaled cell totals of `t * mu`, and every entry must be within `eta` times its cell total of `t * mu`. Take also any source `S` that contains the parent-graded typical band, at the tight tolerance, of every triple of `good` histograms.
--
--   Then there is a graded part stage (`LogPartStageG`) with the following properties:
--   - its source is `S`;
--   - its target is: the word is graded at `a`, and its histogram satisfies `good`;
--   - its rate is `c t`;
--   - it has at most `(|Position| + 1)^(3 |Cell| |W|)` types.
--
--   The types are the exact histogram triples of supported graded words. Each type's step is a graded-source integer step at the common rate.
--
--   This is the recursive analogue of the global histogram-window stage family, and it is what lets a hashing stage follow an interface described by a histogram window.
-- source:
--   Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication (https://arxiv.org/abs/2404.16349), sections 5-6: a recursive hashing stage over all histogram types near the prescribed distribution. Exact asymptotic statement as written; no exponent claim.

import Mathlib
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_dwz_profiled_regional_positions_data
open BigOperators Filter MME MME.RecursiveYZ MME.RegionRate MME.RegionRealization MME.DWZProfiledRegional
set_option autoImplicit false

theorem mme_graded_band_part_stage {ell R : ℕ}
    (parent : Fin R → Fin 3 → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * (2 * 2 ^ (ell - 1)))
    (n : Fin R → ℕ) (hn : ∀ r, 0 < n r) (hR : 0 < R)
    (m : ∀ r, RecursiveThinSplit.Split (2 * 2 ^ (ell - 1)) (parent r) → ℕ)
    (hm : ∀ r, ∑ c, m r c = n r)
    (mu : Fin 3 → Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < regionalRate htotal n m mu) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ t : ℕ in atTop,
      ∀ a : Address (2 * 2 ^ (ell - 1)) R parent (fun r ↦ t * n r),
        a ∈ RecursiveXHash.target (n := fun r ↦ t * n r) (fun r c ↦ t * m r c) →
      ∀ good : Fin 3 → (Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ) → Prop,
        (∀ i mu'', good i mu'' → (∀ c, ∑ w, mu'' c w = ∑ w, t * mu i c w) ∧
          ∀ c w, |(mu'' c w : ℝ) - ((t * mu i c w : ℕ) : ℝ)| ≤ η * ((∑ z, t * mu i c z : ℕ) : ℝ)) →
      ∀ S : ProfiledCW.Predicate (lenAt n t * 2 ^ (ell - 1)),
        (∀ mu' : Fin 3 → Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ,
          (∀ i, good i (mu' i)) → ∀ i x,
          ParentGraded parent (fun r ↦ t * n r) i (ProfiledCW.split (positionsAt n t) rfl x) →
          parentTypical htotal (fun r ↦ t * n r) (fun r c ↦ t * m r c) (mu' i)
            (Real.sqrt (8 * (25 * (R : ℝ) * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) *
              ((Nat.sqrt t + 2 : ℕ) : ℝ) / t))
            (ProfiledCW.split (positionsAt n t) rfl x) → S i x) →
        ∃ D : LogPartStageG (lenAt n t * 2 ^ (ell - 1)) ell S
            (fun i y ↦ Graded htotal i a (ProfiledCW.split (positionsAt n t) rfl y) ∧
              good i (count (fullCell htotal a) (ProfiledCW.split (positionsAt n t) rfl y))),
          D.types ≤ (Fintype.card (Position (fun r ↦ t * n r)) + 1) ^
            (3 * Fintype.card (Cell (2 * 2 ^ (ell - 1)) R parent) *
              Fintype.card (CompleteSplit.CompleteWord ell)) ∧
          D.rate = c * t := by sorry
