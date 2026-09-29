-- Prove2me | Theorems.Thm_mme_dwz_global_exact_profile_candidate_budget_reindexed
-- name    : mme_dwz_global_exact_profile_candidate_budget_reindexed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T01:57:27.855533+00:00
-- url     : https://prove2.me/theorems/c01f920d-1430-4960-b50f-29394d7f67ff
-- title:
--   The uniform Claim-6.8 candidate bound survives canonical source reindexing
-- statement:
--   Let $L=m\,\mathrm{scale}$ with $m>0$, put $N=L-1$, and identify the affine coordinate set $[N+1]$ with the native source coordinate set $[L]$. For a native exact-profile owner $u$ and useful block $z$, let $C(u,z)$ be the exact-profile competitors that share the complete coarse-$Z$ word and satisfy the DWZ retained fine-compatibility condition. If one prime $p$ obeys
--
--   $$
--   8|C(u,z)|\le p
--   $$
--
--   for every native owner and useful block, then the identical bound holds for every exact-profile owner written in the canonically reindexed affine coordinates. This transport incurs no change in the competitor family and no loss in the constant.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Claim 6.8 (printed pp. 56–57; PDF pp. 57–58) and the source-coordinate setup in Section 6; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_retained_fine_compatibility
import Definitions.Def_mme_dwz_table2_useful_block

set_option autoImplicit false

theorem mme_dwz_global_exact_profile_candidate_budget_reindexed
    (m : ℕ) (hm : 0 < m) {p : ℕ} :
    let L := MME.DWZTable2Counts.scale * m
    let N := L - 1
    let reindex : Fin (N + 1) ≃ Fin L := finCongr (by
      dsimp only [N, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let ExactProfile : (Fin (N + 1) → Fin 15) → Prop := fun a ↦
      ∀ s, Fintype.card {t : Fin (N + 1) // a t = s} =
        MME.DWZTable2Counts.component s * m
    let ExactProfileNative : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m
    let T : Finset (Fin (N + 1) → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfile
    let Tnative : Finset (Fin L → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfileNative
    let NativeOwner := {w : Fin L → Fin 15 // ExactProfileNative w}
    let native : (Fin (N + 1) → Fin 15) → Fin L → Fin 15 :=
      fun a t ↦ a (reindex.symm t)
    let grade : ∀ a,
        MME.DWZTable2StandardForm.UsefulBlock m (native a) →
          Fin L → Fin (3 * 3) := fun _ z t ↦
      MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
    (∀ retained : NativeOwner,
      ∀ z : MME.DWZTable2StandardForm.UsefulBlock m retained.1,
        8 * ((by
          classical
          exact Tnative.filter (fun w : Fin L → Fin 15 ↦
            (∀ t, MME.DWZSquare.shapeZ (w t) =
              MME.DWZSquare.shapeZ (retained.1 t)) ∧
            MME.DWZStep2Source.retainedFineCompatible m
              (fun w : Fin L → Fin 15 ↦ w)
              (fun t ↦ MME.DWZStep1Support.fineSplitGrade
                (z.1 t).1 (z.1 t).2) w)) :
          Finset (Fin L → Fin 15)).card ≤ p) →
    ∀ a, a ∈ T →
      ∀ z : MME.DWZTable2StandardForm.UsefulBlock m (native a),
        8 * ((by
          classical
          exact Tnative.filter (fun w : Fin L → Fin 15 ↦
            (∀ t, MME.DWZSquare.shapeZ (w t) =
              MME.DWZSquare.shapeZ (native a t)) ∧
            MME.DWZStep2Source.retainedFineCompatible m
              (fun w : Fin L → Fin 15 ↦ w) (grade a z) w)) :
          Finset (Fin L → Fin 15)).card ≤ p := by
  sorry
