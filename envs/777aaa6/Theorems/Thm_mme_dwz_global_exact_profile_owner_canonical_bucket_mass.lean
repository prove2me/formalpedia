-- Prove2me | Theorems.Thm_mme_dwz_global_exact_profile_owner_canonical_bucket_mass
-- name    : mme_dwz_global_exact_profile_owner_canonical_bucket_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T07:39:55.871323+00:00
-- url     : https://prove2.me/theorems/9af16687-3028-4fab-8773-554365e8fd09
-- title:
--   Exact-profile owner aggregate mass on its canonical affine bucket
-- statement:
--   Fix a positive Table-2 scale, an odd prime greater than four, a lower-half three-term-progression-free set S, and one exact-profile owner a in the global marginal family A. If the common prime bounds every fine compatible-candidate fiber, then the aggregate Claim 6.8 nonhole mass for that owner, summed over literal canonical affine bucket states containing a, is at least seven eighths of the full S-by-weight-by-useful-block incidence mass. The theorem identifies canonical bucket membership with affine retaining-state membership and keeps the same common affine state needed by the later global selector.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 6.1 and Claim 6.8.

import Theorems.Thm_mme_dwz_global_exact_profile_owner_conditioned_weight_mass
import Theorems.Thm_mme_dwz_table2_affine_hash_bucket_mem_iff_retains
import Definitions.Def_mme_dwz_global_ambient_conditioned_broken_copy

open MME BigOperators

set_option autoImplicit false

theorem mme_dwz_global_exact_profile_owner_canonical_bucket_mass
    (m : ℕ) (hm : 0 < m)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hp4 : 4 < p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset
      (Fin ((MME.DWZTable2Counts.scale * m - 1) + 1) → Fin 15))
    (a : Fin ((MME.DWZTable2Counts.scale * m - 1) + 1) → Fin 15)
    (haA : a ∈ A)
    (hprofile : ∀ s,
      Fintype.card
          {t : Fin ((MME.DWZTable2Counts.scale * m - 1) + 1) //
            a t = s} =
        MME.DWZTable2Counts.component s * m) :
    let L := MME.DWZTable2Counts.scale * m
    let n := L - 1
    let reindex : Fin (n + 1) ≃ Fin L := finCongr (by
      dsimp only [n, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let retained : Fin L → Fin 15 := fun t ↦ a (reindex.symm t)
    let ExactProfile : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m
    let T : Finset (Fin L → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfile
    let grade : MME.DWZTable2StandardForm.UsefulBlock m retained →
        Fin L → Fin (3 * 3) := fun z t ↦
      MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
    let candidates : MME.DWZTable2StandardForm.UsefulBlock m retained →
        Finset (Fin L → Fin 15) := fun z ↦ by
      classical
      exact T.filter (fun w : Fin L → Fin 15 ↦
        (∀ t, MME.DWZSquare.shapeZ (w t) =
          MME.DWZSquare.shapeZ (retained t)) ∧
        MME.DWZStep2Source.retainedFineCompatible m
          (fun w : Fin L → Fin 15 ↦ w) (grade z) w)
    let hretainedT : retained ∈ T := by
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and,
        ExactProfile]
      intro s
      let E : {t : Fin L // retained t = s} ≃
          {t : Fin (n + 1) // a t = s} :=
        reindex.symm.subtypeEquiv (fun _ ↦ Iff.rfl)
      calc
        Fintype.card {t : Fin L // retained t = s} =
            Fintype.card {t : Fin (n + 1) // a t = s} :=
          Fintype.card_congr E
        _ = MME.DWZTable2Counts.component s * m := hprofile s
    (∀ z, 8 * (candidates z).card ≤ p) →
      7 * S.card * p ^ (n + 1) *
          Fintype.card
            (MME.DWZTable2StandardForm.UsefulBlock m retained) ≤
        8 * ∑ q ∈ (Finset.univ.filter (fun q :
            (Fin (n + 2) → ZMod p) × ZMod p ↦
          a ∈ MME.dwzTable2AffineHashBucket S A q)),
          (MME.DWZGlobalCorrelated.ambientConditionedBrokenCopy
            m reindex T retained hretainedT
            (fun t ↦ q.1 t.castSucc)).nonholes.card := by
  sorry
