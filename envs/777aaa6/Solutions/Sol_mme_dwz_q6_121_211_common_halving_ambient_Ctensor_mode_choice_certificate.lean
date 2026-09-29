-- Prove2me | solution 1 for mme_dwz_q6_121_211_common_halving_ambient_Ctensor_mode_choice_certificate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:42:37.777499+00:00
-- url     : https://prove2.me/submissions/2ccb563b-9be2-480e-88b4-53c28eddeece
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Tactic
import Theorems.Thm_mme_tensorProduct_basis_filter_absorption
import Theorems.Thm_mme_dwz_q6_121_211_common_halving_ambient_Ctensor_mode_choice_vanishing_certificate

open MME Module TensorProduct
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {K : Type u} [Field K]
    (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily
      (MME.DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving) :
    ∃ star : Fin A → TensorObj K 3,
      ∃ cert : InducedModeChoiceCertificate
        (componentPairAmbient K s m) (TensorObj.bigAdd star),
        (∀ (i : Fin 3) (slot : Fin (cert.slotCount i)),
          (cert.modeMap i slot).comp (componentPairProject K s m i) =
            cert.modeMap i slot) ∧
        Nonempty (∀ a : Fin A,
          CTensorOneHOneCertificate (star a) H
            (6 ^ (4 * G + 2 * L))) := by
  classical
  obtain ⟨star, cert, hvanish, hstar⟩ :=
    mme_dwz_q6_121_211_common_halving_ambient_Ctensor_mode_choice_vanishing_certificate
      (K := K) s hs m L G A H family halving
  refine ⟨star, cert, ?_, hstar⟩
  intro i slot
  fin_cases i
  · have hproject :
        componentPairProject K s m 0 = LinearMap.id := by
      simp [componentPairProject, componentPowerProject,
        swapFirstTwoPerm]
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => rfl
      | add x y hx hy => simp [hx, hy]
    change (cert.modeMap 0 slot).comp
      (componentPairProject K s m 0) = cert.modeMap 0 slot
    rw [hproject]
    apply LinearMap.ext
    intro z
    rfl
  · have hproject :
        componentPairProject K s m 1 = LinearMap.id := by
      simp [componentPairProject, componentPowerProject,
        swapFirstTwoPerm]
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.induction_on with
      | zero => simp
      | tmul x y => rfl
      | add x y hx hy => simp [hx, hy]
    change (cert.modeMap 1 slot).comp
      (componentPairProject K s m 1) = cert.modeMap 1 slot
    rw [hproject]
    apply LinearMap.ext
    intro z
    rfl
  · simpa [componentPairProject, componentPowerProject,
      swapFirstTwoPerm] using
      (mme_tensorProduct_basis_filter_absorption
        (componentPowerZBasis K s m) (componentPowerZBasis K s m)
        (componentWordAllowed s m) (componentWordAllowed s m)
        (cert.modeMap 2 slot) (hvanish slot))
