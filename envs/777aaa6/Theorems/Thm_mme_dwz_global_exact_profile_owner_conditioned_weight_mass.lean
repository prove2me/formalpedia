-- Prove2me | Theorems.Thm_mme_dwz_global_exact_profile_owner_conditioned_weight_mass
-- name    : mme_dwz_global_exact_profile_owner_conditioned_weight_mass
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T00:01:38.526441+00:00
-- url     : https://prove2.me/theorems/84eff7f5-b79d-4594-b13c-9c37300f40f6
-- title:
--   Ownerwise aggregate Claim 6.8 mass on the full exact-profile family
-- statement:
--   Fix an exact-profile Table-2 owner and let the competitor universe consist of every exact-profile word with the same complete coarse-Z word. Suppose one odd prime controls the compatible-candidate family for every useful fine block. Then, after conditioning the second hash on the retained owner, the total number of nonholes over all affine states retaining that owner is at least seven eighths of the full label-weight-block mass. In division-free form, 7|S|p^L|B| is at most eight times the sum of the nonhole cardinalities. The affine state remains common in the later weighted selection; this theorem only establishes the ownerwise incidence mass.
-- source:
--   Duan--Wu--Zhou, Claim 6.8 and the aggregate asymmetric-hash incidence count.

import Theorems.Thm_mme_dwz_global_exact_profile_claim6_8_bad_weight_bound
import Theorems.Thm_mme_dwz_asymmetric_hash_retaining_states_broken_copy_mass
import Theorems.Thm_mme_dwz_table2_useful_block_typical_and_compatible
import Theorems.Thm_mme_lower_half_ZMod_image_card
import Definitions.Def_mme_dwz_table2_affine_hash_bucket

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_global_exact_profile_owner_conditioned_weight_mass
    (m : ℕ) (hm : 0 < m)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hlevel : 4 < p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (retained : Fin (MME.DWZTable2Counts.scale * m) → Fin 15)
    (hretained : ∀ s,
      Fintype.card
          {t : Fin (MME.DWZTable2Counts.scale * m) // retained t = s} =
        MME.DWZTable2Counts.component s * m) :
    let L := MME.DWZTable2Counts.scale * m
    let n := L - 1
    let reindex : Fin (n + 1) ≃ Fin L := finCongr (by
      dsimp only [n, L]
      exact Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by decide) (Nat.ne_of_gt hm))))
    let ExactProfile : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ s, Fintype.card {t : Fin L // w t = s} =
        MME.DWZTable2Counts.component s * m
    let T : Finset (Fin L → Fin 15) := by
      classical
      exact Finset.univ.filter ExactProfile
    let sameZ : (Fin L → Fin 15) → Prop := fun w ↦
      ∀ t, MME.DWZSquare.shapeZ (w t) =
        MME.DWZSquare.shapeZ (retained t)
    let Outer := {w : Fin L → Fin 15 // w ∈ T ∧ sameZ w}
    let grade : MME.DWZTable2StandardForm.UsefulBlock m retained →
        Fin L → Fin (3 * 3) := fun z t ↦
      MME.DWZStep1Support.fineSplitGrade (z.1 t).1 (z.1 t).2
    let compatible : MME.DWZTable2StandardForm.UsefulBlock m retained →
        Outer → Prop := fun z A ↦
      MME.DWZStep2Source.retainedFineCompatible m
        (fun w : Fin L → Fin 15 ↦ w) (grade z) A.1
    let addressX : Outer → Fin (n + 1) → Fin 5 := fun A t ↦
      MME.DWZSquare.shapeX (A.1 (reindex t))
    let addressZ : Fin (n + 1) → Fin 5 := fun t ↦
      MME.DWZSquare.shapeZ (retained (reindex t))
    let b0 : ZMod p := 0
    let hX : (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin 5) → ZMod p := fun w X ↦
      b0 + ∑ t, ((X t).val : ZMod p) * w t
    let hZ : ZMod p → (Fin (n + 1) → ZMod p) →
        (Fin (n + 1) → Fin 5) → ZMod p := fun w0 w Z ↦
      b0 + (2 : ZMod p)⁻¹ *
        (w0 + ∑ t, ((4 : ZMod p) - (Z t).val) * w t)
    let conditionedW0 : (Fin (n + 1) → ZMod p) → ZMod p := fun w ↦
      2 * (∑ t,
        (((MME.DWZSquare.shapeX (retained (reindex t))).val : ℕ) :
          ZMod p) * w t) -
        ∑ t, ((4 : ZMod p) - (addressZ t).val) * w t
    let hashRetained : Outer → (Fin (n + 1) → ZMod p) → Prop :=
      fun A w ↦ hX w (addressX A) =
        hZ (conditionedW0 w) w addressZ
    let retainedOuter : Outer := by
      refine ⟨retained, ?_, fun _ ↦ rfl⟩
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and,
        ExactProfile]
      exact hretained
    let weightCopy : (Fin (n + 1) → ZMod p) →
        MME.DWZSquare.BrokenBlockCopy
          (MME.DWZTable2StandardForm.UsefulBlock m retained) := by
      classical
      exact fun w ↦ MME.DWZStep2.brokenCopy
        (fun z A ↦ compatible z A ∧ hashRetained A w)
        (fun _ _ ↦ True) retainedOuter
    let castS : Finset (ZMod p) :=
      S.image (fun a : ℕ ↦ (a : ZMod p))
    let candidates : MME.DWZTable2StandardForm.UsefulBlock m retained →
        Finset (Fin L → Fin 15) := fun z ↦ by
      classical
      exact T.filter (fun w ↦ sameZ w ∧
        MME.DWZStep2Source.retainedFineCompatible m
          (fun w : Fin L → Fin 15 ↦ w) (grade z) w)
    (∀ z, 8 * (candidates z).card ≤ p) →
      7 * S.card * p ^ (n + 1) *
          Fintype.card
            (MME.DWZTable2StandardForm.UsefulBlock m retained) ≤
        8 * ∑ q ∈ MME.dwzAsymmetricAffineStatesRetaining
            (4 : ZMod p) castS
            (MME.dwzTable2CastX (fun t ↦ retained (reindex t)))
            (MME.dwzTable2CastY (fun t ↦ retained (reindex t)))
            (MME.dwzTable2CastZ (fun t ↦ retained (reindex t))),
          (weightCopy (fun t ↦ q.1 t.castSucc)).nonholes.card := by

  sorry
