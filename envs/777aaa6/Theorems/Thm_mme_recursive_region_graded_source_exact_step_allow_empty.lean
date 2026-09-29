-- Prove2me | Theorems.Thm_mme_recursive_region_graded_source_exact_step_allow_empty
-- name    : mme_recursive_region_graded_source_exact_step_allow_empty
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T03:27:33.665133+00:00
-- url     : https://prove2.me/theorems/adaf717a-8094-402a-8340-20c0b7d11a78
-- title:
--   Exact regional extraction allowing empty regions
-- statement:
--   The graded regional exact extraction theorem remains valid when some regions are empty. The minimum size k is required only for nonempty regions. Empty regions have zero empirical and target frequencies and contribute no concentration failure. The target-cardinality lower bound, common hash scale, repair exponent, and graded useful output are unchanged. All mass, support, boundary, divisibility, scale and source-inclusion hypotheses remain explicit.
-- source:
--   Prescribed-cell parent concentration, regional hole budgets, computed hash selection and exact profiled CW extraction.

import Definitions.Def_mme_recursive_profiled_CW_data
import Theorems.Thm_mme_recursive_region_computed_hash_selection
import Mathlib.Data.Nat.Log
import Theorems.Thm_mme_prescribed_cell_pair_pattern_concentration
import Theorems.Thm_mme_prescribed_cell_histogram_nonempty
import Definitions.Def_mme_recursive_region_parent_profiles
import Theorems.Thm_mme_prescribed_cell_parent_profile_concentration
import Theorems.Thm_mme_recursive_region_parent_profile_concentration
import Definitions.Def_mme_recursive_yz_hash_filter
open BigOperators MME.RecursiveYZ
open scoped Classical
open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.ProfiledCW
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open MME.ProfiledCW MME.RecursiveYZ.CWCells
set_option autoImplicit false
universe u

theorem mme_recursive_region_graded_source_exact_step_allow_empty {half R ell N L M : ℕ}
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (hhalf : half = 2 * 2 ^ (ell - 1))
    (m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ)
    (e : Fin (N + 1) ≃ (r : Fin R) × Fin (n r))
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (ell - 1) = M)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (hsupport : ∀ i c w, 0 < mu i c w → ∑ h, (w h).val = (c.2.val i).val)
    (hboundary : BoundaryProfiles mu)
    (reference : Address half R parent n) (href : reference ∈ RecursiveXHash.target m)
    (k d : ℕ) (hk : 0 < k) (hd : 1 < d) (hkn : ∀ r, n r ≠ 0 → k ≤ n r) (hdiv : ∀ r c, k ∣ m r c)
    (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * R * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) ≤
      (k : ℝ) * eps ^ 2)
    (source : Predicate M)
    (hsource : ∀ i (a : Address half R parent n), a ∈ RecursiveXHash.target m →
      ∀ f : Position n → CompleteSplit.CompleteWord ell,
        Graded htotal i a f → parentTypical htotal n m (mu i) eps f →
        source i (ProfiledCW.flatten positions length f)) :
    let keep := fun (i : Fin 2) (_ : Address half R parent n) ↦ parentTypical htotal n m (mu (yzMode i)) eps
    let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i)) keep) (loadDen m)
    let cap := ∏ i : Fin 3, Nat.card (Block ell (fullCell htotal reference) (fun c i ↦ (c.2.val i).val) mu i)
    ∃ E : ExactStep ell M source,
      ((RecursiveXHash.target (n := n) m).card : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
      E.stage.repairExponent = Nat.log d cap + 1 ∧
      E.output = fun i x ↦ Graded htotal i reference (ProfiledCW.split positions length x) ∧
        Useful (fullCell htotal reference) (mu i) (ProfiledCW.split positions length x) := by sorry
