-- Prove2me | Theorems.Thm_mme_dwz_global_exact_profile_claim6_8_bad_weight_bound
-- name    : mme_dwz_global_exact_profile_claim6_8_bad_weight_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T23:40:21.889389+00:00
-- url     : https://prove2.me/theorems/dc3a6356-c99a-477f-986a-43f3878f4fc6
-- title:
--   Claim 6.8 bad-weight bound on the full exact-profile family
-- statement:
--   Fix a Table-2 word with the prescribed fifteen-component profile and a useful fine block over it. Among all exact-profile words, retain only those with the same complete coarse-Z word and satisfying the fine compatibility equations. If one common odd prime p satisfies eight times the size of this global candidate set at most p, then at most one eighth of the affine weight words admit more than one compatible conditioned-hash survivor. Thus the fixed-coarse-Z collision estimate of Claim 6.8 transports faithfully to the global exact-profile family.
-- source:
--   Duan--Wu--Zhou, Claim 6.8; global exact-profile/fixed-coarse-Z transport.

import Theorems.Thm_mme_dwz_table2_claim6_8_explicit_collision_fiber_bound
import Theorems.Thm_mme_dwz_table2_useful_block_typical_and_compatible
import Theorems.Thm_mme_bad_weight_card_mono_of_injective_candidate_map
import Definitions.Def_mme_dwz_retained_fine_compatibility

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_global_exact_profile_claim6_8_bad_weight_bound
    (m : ℕ) (hm : 0 < m)
    {p : ℕ} [Fact p.Prime] (hpodd : Odd p) (hlevel : 4 < p)
    (retained : Fin (MME.DWZTable2Counts.scale * m) → Fin 15)
    (hretained : ∀ s,
      Fintype.card
          {t : Fin (MME.DWZTable2Counts.scale * m) // retained t = s} =
        MME.DWZTable2Counts.component s * m)
    (small : MME.DWZTable2StandardForm.UsefulBlock m retained)
    (b0 : ZMod p) :
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
    let grade : Fin L → Fin (3 * 3) := fun t ↦
      MME.DWZStep1Support.fineSplitGrade
        (small.1 t).1 (small.1 t).2
    let fineCompatible : (Fin L → Fin 15) → Prop := fun w ↦
      MME.DWZStep2Source.retainedFineCompatible m
        (fun w : Fin L → Fin 15 ↦ w) grade w
    let candidates : Finset (Fin L → Fin 15) := by
      classical
      exact T.filter (fun w ↦ sameZ w ∧ fineCompatible w)
    let GlobalOuter := {w : Fin L → Fin 15 // w ∈ T ∧ sameZ w}
    let addressX : GlobalOuter → Fin (n + 1) → Fin 5 := fun w t ↦
      MME.DWZSquare.shapeX (w.1 (reindex t))
    let addressZ : Fin (n + 1) → Fin 5 := fun t ↦
      MME.DWZSquare.shapeZ (retained (reindex t))
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
    let hashRetained : GlobalOuter →
        (Fin (n + 1) → ZMod p) → Prop := fun A w ↦
      hX w (addressX A) = hZ (conditionedW0 w) w addressZ
    let bad : Finset (Fin (n + 1) → ZMod p) := by
      classical
      exact Finset.univ.filter (fun w ↦
        1 < (Finset.univ.filter (fun A : GlobalOuter ↦
          fineCompatible A.1 ∧ hashRetained A w)).card)
    8 * candidates.card ≤ p →
      8 * bad.card ≤
        Fintype.card (Fin (n + 1) → ZMod p) := by

  sorry
