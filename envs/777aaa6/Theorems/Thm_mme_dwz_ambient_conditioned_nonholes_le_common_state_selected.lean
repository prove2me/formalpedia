-- Prove2me | Theorems.Thm_mme_dwz_ambient_conditioned_nonholes_le_common_state_selected
-- name    : mme_dwz_ambient_conditioned_nonholes_le_common_state_selected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T02:55:54.390653+00:00
-- url     : https://prove2.me/theorems/01c28271-7f3b-4959-b6a3-62a6c1e43bf8
-- title:
--   Ambient conditioned DWZ nonholes survive canonical family selection
-- statement:
--   Fix an exact-profile Table-2 owner retained by one affine state, and injectively enumerate a selected family of exact-profile owners. The ambient conditioned broken copy compares the owner with every exact-profile competitor having its coarse-Z word, whereas the selected common-state broken copy compares it only with owners in the enumerated family. Then selection cannot decrease the number of nonholes:
--
--   $$
--   |\operatorname{nonholes}(B_{\mathrm{amb}})| \le |\operatorname{nonholes}(B_{\mathrm{sel}})|.
--   $$
--
--   The result is the exact competitor-monotonicity bridge from aggregate Claim 6.8 incidence counting to the literal common-state family used by the source restriction.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Step 2, Definition 6.3, and Claim 6.8, printed pp. 51--55; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Definitions.Def_mme_dwz_global_ambient_conditioned_broken_copy
import Theorems.Thm_mme_dwz_step2_broken_copy_nonholes_card_mono_of_injective_map
import Theorems.Thm_mme_dwz_step2_broken_copy_nonholes_card_eq_subtype_of_compatible
import Theorems.Thm_mme_dwz_affine_common_state_XZ_iff_conditioned

open MME BigOperators

set_option autoImplicit false

/-!
# Ambient conditioned mass survives selected-family restriction

The Claim-6.8 mass is first counted against every exact-profile competitor
with the owner's coarse Z word.  The final source family contains only the
enumerated selected owners.  This theorem is the exact termwise monotonicity
bridge between those two broken copies.
-/

theorem mme_dwz_ambient_conditioned_nonholes_le_common_state_selected
    (m : ℕ) {p N L k : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (reindex : Fin (N + 1) ≃ Fin L)
    (S : Finset (ZMod p))
    (T : Finset (Fin L → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin k → Fin (N + 1) → Fin 15)
    (hedgeT : ∀ j, MME.DWZGlobalCorrelated.sourceWord reindex edge j ∈ T)
    (hedgeInjective : Function.Injective edge)
    (r : Fin k)
    (hretains : MME.dwzAsymmetricAffineRetains (4 : ZMod p) S
      (MME.dwzTable2CastX (edge r))
      (MME.dwzTable2CastY (edge r))
      (MME.dwzTable2CastZ (edge r)) q) :
    let retained := MME.DWZGlobalCorrelated.sourceWord reindex edge r
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
    let weight : Fin (N + 1) → ZMod p := fun t ↦ q.1 t.castSucc
    let addressX : Outer → Fin (N + 1) → Fin 5 := fun A t ↦
      MME.DWZSquare.shapeX (A.1 (reindex t))
    let addressZ : Fin (N + 1) → Fin 5 := fun t ↦
      MME.DWZSquare.shapeZ (retained (reindex t))
    let conditionedW0 : ZMod p :=
      2 * (∑ t,
        (((MME.DWZSquare.shapeX (retained (reindex t))).val : ℕ) :
          ZMod p) * weight t) -
        ∑ t, ((4 : ZMod p) - (addressZ t).val) * weight t
    let hashRetained : Outer → Prop := fun A ↦
      (∑ t, (((addressX A) t).val : ZMod p) * weight t) =
        (2 : ZMod p)⁻¹ *
          (conditionedW0 +
            ∑ t, ((4 : ZMod p) - (addressZ t).val) * weight t)
    let retainedOuter : Outer := by
      refine ⟨retained, hedgeT r, ?_⟩
      intro t
      rfl
    let ambientCopy : MME.DWZSquare.BrokenBlockCopy
        (MME.DWZTable2StandardForm.UsefulBlock m retained) := by
      classical
      exact MME.DWZStep2.brokenCopy
        (fun z A ↦ compatible z A ∧ hashRetained A)
        (fun _ _ ↦ True) retainedOuter
    ambientCopy.nonholes.card ≤
      (MME.DWZGlobalCorrelated.commonStateBrokenCopy
        m reindex q edge r).nonholes.card := by
  sorry
