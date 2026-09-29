-- Prove2me | solution 1 for mme_dwz_prescribed_z_power_one_class_profile_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T16:55:38.738753+00:00
-- url     : https://prove2.me/submissions/1bd3944c-7226-4379-a311-1b95f47b61d9

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Definitions.Def_mme_tensor_bridge

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue Module

universe u

set_option autoImplicit false

/-!
# A one-class prescribed Z profile keeps the whole power

When the Z grade takes a single value, every word of `T^{⊗ p.length m}` has the prescribed
left-grade histogram, so the prescribed Z power is the whole power rather than a proper
projection of it. This is the converse direction of `mme_dwz_prescribed_z_power_projection`,
available only in this degenerate case, and it is what lets a terminal node of a recursive
prescribed-Z ledger be stated with a trivial profile.
-/

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin 1)
    (p : IntegerZSplitProfile 1) (m : ℕ) :
    TensorObj.Restrict (T.kronPow (p.length m))
      (prescribedZPower T bZ grade p m) := by
  classical
  have hcount : p.count 0 = p.denominator := by
    have := p.count_sum
    simpa using this
  refine @mme_restrict_basisZAllowedSubtensor_of_vanishes K _
    (T.kronPow (p.length m)) (T.kronPow (p.length m))
    (PowIndex ι (p.length m))
    (kronPowModeBasis T 2 bZ (p.length m))
    (prescribedZWord grade p m)
    (fun _ ↦ Classical.propDecidable _)
    (fun _ ↦ LinearMap.id) ?_ ?_
  · exact LinearMap.congr_fun (PiTensorProduct.map_id (R := K)) _
  · intro w hnot
    exfalso
    apply hnot
    intro a
    have ha : a = 0 := Subsingleton.elim a 0
    subst ha
    -- every letter has the single available grade, so the count is the whole length
    have hall : ∀ r : Fin (p.length m), grade (PowIndex.get (p.length m) w r) = 0 :=
      fun r ↦ Subsingleton.elim _ _
    have hcard : (Finset.univ.filter
        (fun r : Fin (p.length m) ↦ grade (PowIndex.get (p.length m) w r) = 0)).card
        = p.length m := by
      rw [Finset.filter_true_of_mem (fun r _ ↦ hall r), Finset.card_univ, Fintype.card_fin]
    calc leftGradeCount grade w 0 = p.length m := hcard
      _ = p.count 0 * m := by
          rw [hcount]
          rfl
