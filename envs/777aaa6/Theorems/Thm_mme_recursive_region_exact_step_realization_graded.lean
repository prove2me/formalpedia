-- Prove2me | Theorems.Thm_mme_recursive_region_exact_step_realization_graded
-- name    : mme_recursive_region_exact_step_realization_graded
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-22T15:41:08.163385+00:00
-- url     : https://prove2.me/theorems/078a59b3-b625-4595-bc27-9570b0243944
-- title:
--   Exact step realization with a parent-graded typical source
-- statement:
--   This is the exact-step realization of a regional hashing step, with a weaker requirement on the source. Fix integer regional data: parent types and counts, split counts divisible by `k` with `k` at most every parent count, complete-word histograms satisfying the mass, support and boundary-profile conditions, a target reference address, a repair base `d > 1`, and a tolerance `eps` satisfying the size test.
--
--   Let `P` be any source predicate that contains the flattening of every word which is both **parent-graded** and typical for the parent mixture at tolerance `eps`. Parent-graded means that, in every parent occurrence, the two halves' grades add up to the parent's grade.
--
--   Then there is an exact step with source `P`. Its selected-family count is at least the usual incidence lower bound, its repair exponent is `log_d` of the block capacity plus one, and its output is the graded, useful projection at the reference address.
--
--   The accepted realization instead requires the source to contain every typical word, including words in which a few parent blocks have the wrong shape. That requirement cannot be met when the source is the output of an earlier exact stage, since such an output fixes every block's shape. The weaker requirement suffices because every unbroken word is parent-graded.
-- source:
--   Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v3: interface tensors fix the level structure exactly and let only complete-split distributions vary (Definitions 3.6 and 4.1); Theorem 6.4, Section 6.6 and Algorithm 1 chain the stages. https://arxiv.org/abs/2404.16349

import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_graded_integer_regional_step_data
open BigOperators MME MME.RecursiveYZ MME.RegionRealization MME.ProfiledCW
  MME.RecursiveYZ.Certificate MME.RecursiveYZ.CWCells
open scoped Classical
set_option autoImplicit false

theorem mme_recursive_region_exact_step_realization_graded {half R ell N L M : ℕ}
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
    (k d : ℕ) (hk : 0 < k) (hd : 1 < d) (hkn : ∀ r, k ≤ n r) (hdiv : ∀ r c, k ∣ m r c)
    (eps : ℝ) (heps : 0 < eps)
    (hscale : (8 * d : ℝ) * (25 * R * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) ≤
      (k : ℝ) * eps ^ 2)
    (P : Predicate M)
    (hP : ∀ i f, ParentGraded parent n i f → parentTypical htotal n m (mu i) eps f →
      P i (ProfiledCW.flatten positions length f)) :
    let keep := fun (i : Fin 2) (_ : Address half R parent n) ↦ parentTypical htotal n m (mu (yzMode i)) eps
    let Q := commonScale half (loadNum htotal m d (fun i ↦ mu (yzMode i)) keep) (loadDen m)
    let cap := ∏ i : Fin 3, Nat.card (Block ell (fullCell htotal reference) (fun c i ↦ (c.2.val i).val) mu i)
    ∃ E : ExactStep ell M P,
      ((RecursiveXHash.target (n := n) m).card : ℝ) * Real.exp (-4 * Real.sqrt (Real.log Q)) / (32 * Q) ≤ E.count ∧
      E.stage.repairExponent = Nat.log d cap + 1 ∧
      E.output = fun i x ↦ Graded htotal i reference (ProfiledCW.split positions length x) ∧
        Useful (fullCell htotal reference) (mu i) (ProfiledCW.split positions length x) := by sorry
