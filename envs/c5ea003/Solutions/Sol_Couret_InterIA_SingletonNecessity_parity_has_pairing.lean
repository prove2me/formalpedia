-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.parity_has_pairing
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:05:36.871546+00:00
-- url     : https://prove2.me/submissions/47779d2d-1ad6-48ba-870e-39cd2db54b6f

import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_ConvolutionParity_aa654fd002fc
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
namespace Couret.InterIA.SingletonNecessity


theorem p2m_local_parity_has_pairing {α : Type*} [DecidableEq α] (d : Fin 6 → α)
    (hp : FibreParity d) : HasPairing d := by
  unfold HasPairing
  by_cases h1_0 : d 1=d 0
  ·
    by_cases h2_0 : d 2=d 0
    ·
      by_cases h3_0 : d 3=d 0
      ·
        by_cases h4_0 : d 4=d 0
        ·
          by_cases h5_0 : d 5=d 0
          ·
            exact Or.inl (⟨by simp only [h1_0, h2_0, h3_0, h4_0, h5_0],by simp only [h1_0, h2_0, h3_0, h4_0, h5_0],by simp only [h1_0, h2_0, h3_0, h4_0, h5_0]⟩)
          ·
            have h := hp (d 0)
            simp [FibreParity, h1_0, h2_0, h3_0, h4_0, h5_0, Ne.symm h5_0] at h
        ·
          by_cases h5_0 : d 5=d 0
          ·
            have h := hp (d 0)
            simp [FibreParity, h1_0, h2_0, h3_0, h5_0, h4_0, Ne.symm h4_0] at h
          ·
            by_cases h5_4 : d 5=d 4
            ·
              exact Or.inl (⟨by simp only [h1_0, h2_0, h3_0, h5_4],by simp only [h1_0, h2_0, h3_0, h5_4],by simp only [h1_0, h2_0, h3_0, h5_4]⟩)
            ·
              have h := hp (d 4)
              simp [FibreParity, h1_0, h2_0, h3_0, h4_0, h5_0, h5_4, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_4] at h
      ·
        by_cases h4_0 : d 4=d 0
        ·
          by_cases h5_0 : d 5=d 0
          ·
            have h := hp (d 0)
            simp [FibreParity, h1_0, h2_0, h4_0, h5_0, h3_0, Ne.symm h3_0] at h
          ·
            by_cases h5_3 : d 5=d 3
            ·
              exact Or.inr (Or.inl (⟨by simp only [h1_0, h2_0, h4_0, h5_3],by simp only [h1_0, h2_0, h4_0, h5_3],by simp only [h1_0, h2_0, h4_0, h5_3]⟩))
            ·
              have h := hp (d 3)
              simp [FibreParity, h1_0, h2_0, h4_0, h3_0, h5_0, h5_3, Ne.symm h3_0, Ne.symm h5_0, Ne.symm h5_3] at h
        ·
          by_cases h4_3 : d 4=d 3
          ·
            by_cases h5_0 : d 5=d 0
            ·
              exact Or.inr (Or.inr (Or.inl (⟨by simp only [h1_0, h2_0, h4_3, h5_0],by simp only [h1_0, h2_0, h4_3, h5_0],by simp only [h1_0, h2_0, h4_3, h5_0]⟩)))
            ·
              by_cases h5_3 : d 5=d 3
              ·
                have h := hp (d 0)
                simp [FibreParity, h1_0, h2_0, h4_3, h5_3, h3_0, h4_0, h5_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h5_0] at h
              ·
                have h := hp (d 0)
                simp [FibreParity, h1_0, h2_0, h4_3, h3_0, h4_0, h5_0, h5_3, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_3] at h
          ·
            by_cases h5_0 : d 5=d 0
            ·
              have h := hp (d 3)
              simp [FibreParity, h1_0, h2_0, h5_0, h3_0, h4_0, h4_3, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_3] at h
            ·
              by_cases h5_3 : d 5=d 3
              ·
                have h := hp (d 0)
                simp [FibreParity, h1_0, h2_0, h5_3, h3_0, h4_0, h4_3, h5_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_3, Ne.symm h5_0] at h
              ·
                by_cases h5_4 : d 5=d 4
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h1_0, h2_0, h5_4, h3_0, h4_0, h4_3, h5_0, h5_3, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_3] at h
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h1_0, h2_0, h3_0, h4_0, h4_3, h5_0, h5_3, h5_4, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_3, Ne.symm h5_4] at h
    ·
      by_cases h3_0 : d 3=d 0
      ·
        by_cases h4_0 : d 4=d 0
        ·
          by_cases h5_0 : d 5=d 0
          ·
            have h := hp (d 0)
            simp [FibreParity, h1_0, h3_0, h4_0, h5_0, h2_0, Ne.symm h2_0] at h
          ·
            by_cases h5_2 : d 5=d 2
            ·
              exact Or.inr (Or.inr (Or.inl (⟨by simp only [h1_0, h3_0, h4_0, h5_2],by simp only [h1_0, h3_0, h4_0, h5_2],by simp only [h1_0, h3_0, h4_0, h5_2]⟩)))
            ·
              have h := hp (d 2)
              simp [FibreParity, h1_0, h3_0, h4_0, h2_0, h5_0, h5_2, Ne.symm h2_0, Ne.symm h5_0, Ne.symm h5_2] at h
        ·
          by_cases h4_2 : d 4=d 2
          ·
            by_cases h5_0 : d 5=d 0
            ·
              exact Or.inr (Or.inl (⟨by simp only [h1_0, h3_0, h4_2, h5_0],by simp only [h1_0, h3_0, h4_2, h5_0],by simp only [h1_0, h3_0, h4_2, h5_0]⟩))
            ·
              by_cases h5_2 : d 5=d 2
              ·
                have h := hp (d 0)
                simp [FibreParity, h1_0, h3_0, h4_2, h5_2, h2_0, h4_0, h5_0, Ne.symm h2_0, Ne.symm h4_0, Ne.symm h5_0] at h
              ·
                have h := hp (d 0)
                simp [FibreParity, h1_0, h3_0, h4_2, h2_0, h4_0, h5_0, h5_2, Ne.symm h2_0, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_2] at h
          ·
            by_cases h5_0 : d 5=d 0
            ·
              have h := hp (d 2)
              simp [FibreParity, h1_0, h3_0, h5_0, h2_0, h4_0, h4_2, Ne.symm h2_0, Ne.symm h4_0, Ne.symm h4_2] at h
            ·
              by_cases h5_2 : d 5=d 2
              ·
                have h := hp (d 0)
                simp [FibreParity, h1_0, h3_0, h5_2, h2_0, h4_0, h4_2, h5_0, Ne.symm h2_0, Ne.symm h4_0, Ne.symm h4_2, Ne.symm h5_0] at h
              ·
                by_cases h5_4 : d 5=d 4
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h1_0, h3_0, h5_4, h2_0, h4_0, h4_2, h5_0, h5_2, Ne.symm h2_0, Ne.symm h4_0, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_2] at h
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h1_0, h3_0, h2_0, h4_0, h4_2, h5_0, h5_2, h5_4, Ne.symm h2_0, Ne.symm h4_0, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_2, Ne.symm h5_4] at h
      ·
        by_cases h3_2 : d 3=d 2
        ·
          by_cases h4_0 : d 4=d 0
          ·
            by_cases h5_0 : d 5=d 0
            ·
              exact Or.inl (⟨by simp only [h1_0, h3_2, h4_0, h5_0],by simp only [h1_0, h3_2, h4_0, h5_0],by simp only [h1_0, h3_2, h4_0, h5_0]⟩)
            ·
              by_cases h5_2 : d 5=d 2
              ·
                have h := hp (d 0)
                simp [FibreParity, h1_0, h3_2, h4_0, h5_2, h2_0, h3_0, h5_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h5_0] at h
              ·
                have h := hp (d 0)
                simp [FibreParity, h1_0, h3_2, h4_0, h2_0, h3_0, h5_0, h5_2, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h5_0, Ne.symm h5_2] at h
          ·
            by_cases h4_2 : d 4=d 2
            ·
              by_cases h5_0 : d 5=d 0
              ·
                have h := hp (d 0)
                simp [FibreParity, h1_0, h3_2, h4_2, h5_0, h2_0, h3_0, h4_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h4_0] at h
              ·
                by_cases h5_2 : d 5=d 2
                ·
                  exact Or.inl (⟨by simp only [h1_0, h3_2, h4_2, h5_2],by simp only [h1_0, h3_2, h4_2, h5_2],by simp only [h1_0, h3_2, h4_2, h5_2]⟩)
                ·
                  have h := hp (d 2)
                  simp [FibreParity, h1_0, h3_2, h4_2, h2_0, h3_0, h4_0, h5_0, h5_2, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_2] at h
            ·
              by_cases h5_0 : d 5=d 0
              ·
                have h := hp (d 0)
                simp [FibreParity, h1_0, h3_2, h5_0, h2_0, h3_0, h4_0, h4_2, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_2] at h
              ·
                by_cases h5_2 : d 5=d 2
                ·
                  have h := hp (d 2)
                  simp [FibreParity, h1_0, h3_2, h5_2, h2_0, h3_0, h4_0, h4_2, h5_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_2, Ne.symm h5_0] at h
                ·
                  by_cases h5_4 : d 5=d 4
                  ·
                    exact Or.inl (⟨by simp only [h1_0, h3_2, h5_4],by simp only [h1_0, h3_2, h5_4],by simp only [h1_0, h3_2, h5_4]⟩)
                  ·
                    have h := hp (d 4)
                    simp [FibreParity, h1_0, h3_2, h2_0, h3_0, h4_0, h4_2, h5_0, h5_2, h5_4, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_2, Ne.symm h5_4] at h
        ·
          by_cases h4_0 : d 4=d 0
          ·
            by_cases h5_0 : d 5=d 0
            ·
              have h := hp (d 2)
              simp [FibreParity, h1_0, h4_0, h5_0, h2_0, h3_0, h3_2, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2] at h
            ·
              by_cases h5_2 : d 5=d 2
              ·
                have h := hp (d 0)
                simp [FibreParity, h1_0, h4_0, h5_2, h2_0, h3_0, h3_2, h5_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h5_0] at h
              ·
                by_cases h5_3 : d 5=d 3
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h1_0, h4_0, h5_3, h2_0, h3_0, h3_2, h5_0, h5_2, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h5_0, Ne.symm h5_2] at h
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h1_0, h4_0, h2_0, h3_0, h3_2, h5_0, h5_2, h5_3, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h5_0, Ne.symm h5_2, Ne.symm h5_3] at h
          ·
            by_cases h4_2 : d 4=d 2
            ·
              by_cases h5_0 : d 5=d 0
              ·
                have h := hp (d 0)
                simp [FibreParity, h1_0, h4_2, h5_0, h2_0, h3_0, h3_2, h4_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h4_0] at h
              ·
                by_cases h5_2 : d 5=d 2
                ·
                  have h := hp (d 2)
                  simp [FibreParity, h1_0, h4_2, h5_2, h2_0, h3_0, h3_2, h4_0, h5_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h5_0] at h
                ·
                  by_cases h5_3 : d 5=d 3
                  ·
                    exact Or.inr (Or.inl (⟨by simp only [h1_0, h4_2, h5_3],by simp only [h1_0, h4_2, h5_3],by simp only [h1_0, h4_2, h5_3]⟩))
                  ·
                    have h := hp (d 3)
                    simp [FibreParity, h1_0, h4_2, h2_0, h3_0, h3_2, h4_0, h5_0, h5_2, h5_3, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_2, Ne.symm h5_3] at h
            ·
              by_cases h4_3 : d 4=d 3
              ·
                by_cases h5_0 : d 5=d 0
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h1_0, h4_3, h5_0, h2_0, h3_0, h3_2, h4_0, h4_2, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_2] at h
                ·
                  by_cases h5_2 : d 5=d 2
                  ·
                    exact Or.inr (Or.inr (Or.inl (⟨by simp only [h1_0, h4_3, h5_2],by simp only [h1_0, h4_3, h5_2],by simp only [h1_0, h4_3, h5_2]⟩)))
                  ·
                    by_cases h5_3 : d 5=d 3
                    ·
                      have h := hp (d 2)
                      simp [FibreParity, h1_0, h4_3, h5_3, h2_0, h3_0, h3_2, h4_0, h4_2, h5_0, h5_2, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_2] at h
                    ·
                      have h := hp (d 2)
                      simp [FibreParity, h1_0, h4_3, h2_0, h3_0, h3_2, h4_0, h4_2, h5_0, h5_2, h5_3, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_2, Ne.symm h5_3] at h
              ·
                by_cases h5_0 : d 5=d 0
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h1_0, h5_0, h2_0, h3_0, h3_2, h4_0, h4_2, h4_3, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_2, Ne.symm h4_3] at h
                ·
                  by_cases h5_2 : d 5=d 2
                  ·
                    have h := hp (d 3)
                    simp [FibreParity, h1_0, h5_2, h2_0, h3_0, h3_2, h4_0, h4_2, h4_3, h5_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_2, Ne.symm h4_3, Ne.symm h5_0] at h
                  ·
                    by_cases h5_3 : d 5=d 3
                    ·
                      have h := hp (d 2)
                      simp [FibreParity, h1_0, h5_3, h2_0, h3_0, h3_2, h4_0, h4_2, h4_3, h5_0, h5_2, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_2, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_2] at h
                    ·
                      by_cases h5_4 : d 5=d 4
                      ·
                        have h := hp (d 2)
                        simp [FibreParity, h1_0, h5_4, h2_0, h3_0, h3_2, h4_0, h4_2, h4_3, h5_0, h5_2, h5_3, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_2, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_2, Ne.symm h5_3] at h
                      ·
                        have h := hp (d 2)
                        simp [FibreParity, h1_0, h2_0, h3_0, h3_2, h4_0, h4_2, h4_3, h5_0, h5_2, h5_3, h5_4, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_2, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_2, Ne.symm h5_3, Ne.symm h5_4] at h
  ·
    by_cases h2_0 : d 2=d 0
    ·
      by_cases h3_0 : d 3=d 0
      ·
        by_cases h4_0 : d 4=d 0
        ·
          by_cases h5_0 : d 5=d 0
          ·
            have h := hp (d 0)
            simp [FibreParity, h2_0, h3_0, h4_0, h5_0, h1_0, Ne.symm h1_0] at h
          ·
            by_cases h5_1 : d 5=d 1
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_0, h3_0, h4_0, h5_1],by simp only [h2_0, h3_0, h4_0, h5_1],by simp only [h2_0, h3_0, h4_0, h5_1]⟩))))))
            ·
              have h := hp (d 1)
              simp [FibreParity, h2_0, h3_0, h4_0, h1_0, h5_0, h5_1, Ne.symm h1_0, Ne.symm h5_0, Ne.symm h5_1] at h
        ·
          by_cases h4_1 : d 4=d 1
          ·
            by_cases h5_0 : d 5=d 0
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_0, h3_0, h4_1, h5_0],by simp only [h2_0, h3_0, h4_1, h5_0],by simp only [h2_0, h3_0, h4_1, h5_0]⟩)))))
            ·
              by_cases h5_1 : d 5=d 1
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_0, h3_0, h4_1, h5_1, h1_0, h4_0, h5_0, Ne.symm h1_0, Ne.symm h4_0, Ne.symm h5_0] at h
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_0, h3_0, h4_1, h1_0, h4_0, h5_0, h5_1, Ne.symm h1_0, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1] at h
          ·
            by_cases h5_0 : d 5=d 0
            ·
              have h := hp (d 1)
              simp [FibreParity, h2_0, h3_0, h5_0, h1_0, h4_0, h4_1, Ne.symm h1_0, Ne.symm h4_0, Ne.symm h4_1] at h
            ·
              by_cases h5_1 : d 5=d 1
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_0, h3_0, h5_1, h1_0, h4_0, h4_1, h5_0, Ne.symm h1_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0] at h
              ·
                by_cases h5_4 : d 5=d 4
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h2_0, h3_0, h5_4, h1_0, h4_0, h4_1, h5_0, h5_1, Ne.symm h1_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1] at h
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h2_0, h3_0, h1_0, h4_0, h4_1, h5_0, h5_1, h5_4, Ne.symm h1_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_4] at h
      ·
        by_cases h3_1 : d 3=d 1
        ·
          by_cases h4_0 : d 4=d 0
          ·
            by_cases h5_0 : d 5=d 0
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_0, h3_1, h4_0, h5_0],by simp only [h2_0, h3_1, h4_0, h5_0],by simp only [h2_0, h3_1, h4_0, h5_0]⟩))))
            ·
              by_cases h5_1 : d 5=d 1
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_0, h3_1, h4_0, h5_1, h1_0, h3_0, h5_0, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h5_0] at h
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_0, h3_1, h4_0, h1_0, h3_0, h5_0, h5_1, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h5_0, Ne.symm h5_1] at h
          ·
            by_cases h4_1 : d 4=d 1
            ·
              by_cases h5_0 : d 5=d 0
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_0, h3_1, h4_1, h5_0, h1_0, h3_0, h4_0, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h4_0] at h
              ·
                by_cases h5_1 : d 5=d 1
                ·
                  exact Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_0, h3_1, h4_1, h5_1],by simp only [h2_0, h3_1, h4_1, h5_1],by simp only [h2_0, h3_1, h4_1, h5_1]⟩))))
                ·
                  have h := hp (d 1)
                  simp [FibreParity, h2_0, h3_1, h4_1, h1_0, h3_0, h4_0, h5_0, h5_1, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1] at h
            ·
              by_cases h5_0 : d 5=d 0
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_0, h3_1, h5_0, h1_0, h3_0, h4_0, h4_1, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1] at h
              ·
                by_cases h5_1 : d 5=d 1
                ·
                  have h := hp (d 1)
                  simp [FibreParity, h2_0, h3_1, h5_1, h1_0, h3_0, h4_0, h4_1, h5_0, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0] at h
                ·
                  by_cases h5_4 : d 5=d 4
                  ·
                    exact Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_0, h3_1, h5_4],by simp only [h2_0, h3_1, h5_4],by simp only [h2_0, h3_1, h5_4]⟩))))
                  ·
                    have h := hp (d 4)
                    simp [FibreParity, h2_0, h3_1, h1_0, h3_0, h4_0, h4_1, h5_0, h5_1, h5_4, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_4] at h
        ·
          by_cases h4_0 : d 4=d 0
          ·
            by_cases h5_0 : d 5=d 0
            ·
              have h := hp (d 1)
              simp [FibreParity, h2_0, h4_0, h5_0, h1_0, h3_0, h3_1, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1] at h
            ·
              by_cases h5_1 : d 5=d 1
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_0, h4_0, h5_1, h1_0, h3_0, h3_1, h5_0, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h5_0] at h
              ·
                by_cases h5_3 : d 5=d 3
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h2_0, h4_0, h5_3, h1_0, h3_0, h3_1, h5_0, h5_1, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h5_0, Ne.symm h5_1] at h
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h2_0, h4_0, h1_0, h3_0, h3_1, h5_0, h5_1, h5_3, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_3] at h
          ·
            by_cases h4_1 : d 4=d 1
            ·
              by_cases h5_0 : d 5=d 0
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_0, h4_1, h5_0, h1_0, h3_0, h3_1, h4_0, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0] at h
              ·
                by_cases h5_1 : d 5=d 1
                ·
                  have h := hp (d 1)
                  simp [FibreParity, h2_0, h4_1, h5_1, h1_0, h3_0, h3_1, h4_0, h5_0, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h5_0] at h
                ·
                  by_cases h5_3 : d 5=d 3
                  ·
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_0, h4_1, h5_3],by simp only [h2_0, h4_1, h5_3],by simp only [h2_0, h4_1, h5_3]⟩)))))
                  ·
                    have h := hp (d 3)
                    simp [FibreParity, h2_0, h4_1, h1_0, h3_0, h3_1, h4_0, h5_0, h5_1, h5_3, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_3] at h
            ·
              by_cases h4_3 : d 4=d 3
              ·
                by_cases h5_0 : d 5=d 0
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h2_0, h4_3, h5_0, h1_0, h3_0, h3_1, h4_0, h4_1, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1] at h
                ·
                  by_cases h5_1 : d 5=d 1
                  ·
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_0, h4_3, h5_1],by simp only [h2_0, h4_3, h5_1],by simp only [h2_0, h4_3, h5_1]⟩))))))
                  ·
                    by_cases h5_3 : d 5=d 3
                    ·
                      have h := hp (d 1)
                      simp [FibreParity, h2_0, h4_3, h5_3, h1_0, h3_0, h3_1, h4_0, h4_1, h5_0, h5_1, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1] at h
                    ·
                      have h := hp (d 1)
                      simp [FibreParity, h2_0, h4_3, h1_0, h3_0, h3_1, h4_0, h4_1, h5_0, h5_1, h5_3, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_3] at h
              ·
                by_cases h5_0 : d 5=d 0
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h2_0, h5_0, h1_0, h3_0, h3_1, h4_0, h4_1, h4_3, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_3] at h
                ·
                  by_cases h5_1 : d 5=d 1
                  ·
                    have h := hp (d 3)
                    simp [FibreParity, h2_0, h5_1, h1_0, h3_0, h3_1, h4_0, h4_1, h4_3, h5_0, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_3, Ne.symm h5_0] at h
                  ·
                    by_cases h5_3 : d 5=d 3
                    ·
                      have h := hp (d 1)
                      simp [FibreParity, h2_0, h5_3, h1_0, h3_0, h3_1, h4_0, h4_1, h4_3, h5_0, h5_1, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_1] at h
                    ·
                      by_cases h5_4 : d 5=d 4
                      ·
                        have h := hp (d 1)
                        simp [FibreParity, h2_0, h5_4, h1_0, h3_0, h3_1, h4_0, h4_1, h4_3, h5_0, h5_1, h5_3, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_3] at h
                      ·
                        have h := hp (d 1)
                        simp [FibreParity, h2_0, h1_0, h3_0, h3_1, h4_0, h4_1, h4_3, h5_0, h5_1, h5_3, h5_4, Ne.symm h1_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_3, Ne.symm h5_4] at h
    ·
      by_cases h2_1 : d 2=d 1
      ·
        by_cases h3_0 : d 3=d 0
        ·
          by_cases h4_0 : d 4=d 0
          ·
            by_cases h5_0 : d 5=d 0
            ·
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_1, h3_0, h4_0, h5_0],by simp only [h2_1, h3_0, h4_0, h5_0],by simp only [h2_1, h3_0, h4_0, h5_0]⟩)))))))
            ·
              by_cases h5_1 : d 5=d 1
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_1, h3_0, h4_0, h5_1, h1_0, h2_0, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h5_0] at h
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_1, h3_0, h4_0, h1_0, h2_0, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h5_0, Ne.symm h5_1] at h
          ·
            by_cases h4_1 : d 4=d 1
            ·
              by_cases h5_0 : d 5=d 0
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_1, h3_0, h4_1, h5_0, h1_0, h2_0, h4_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h4_0] at h
              ·
                by_cases h5_1 : d 5=d 1
                ·
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_1, h3_0, h4_1, h5_1],by simp only [h2_1, h3_0, h4_1, h5_1],by simp only [h2_1, h3_0, h4_1, h5_1]⟩)))))))
                ·
                  have h := hp (d 1)
                  simp [FibreParity, h2_1, h3_0, h4_1, h1_0, h2_0, h4_0, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1] at h
            ·
              by_cases h5_0 : d 5=d 0
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_1, h3_0, h5_0, h1_0, h2_0, h4_0, h4_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h4_0, Ne.symm h4_1] at h
              ·
                by_cases h5_1 : d 5=d 1
                ·
                  have h := hp (d 1)
                  simp [FibreParity, h2_1, h3_0, h5_1, h1_0, h2_0, h4_0, h4_1, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0] at h
                ·
                  by_cases h5_4 : d 5=d 4
                  ·
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_1, h3_0, h5_4],by simp only [h2_1, h3_0, h5_4],by simp only [h2_1, h3_0, h5_4]⟩)))))))
                  ·
                    have h := hp (d 4)
                    simp [FibreParity, h2_1, h3_0, h1_0, h2_0, h4_0, h4_1, h5_0, h5_1, h5_4, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_4] at h
        ·
          by_cases h3_1 : d 3=d 1
          ·
            by_cases h4_0 : d 4=d 0
            ·
              by_cases h5_0 : d 5=d 0
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_1, h3_1, h4_0, h5_0, h1_0, h2_0, h3_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0] at h
              ·
                by_cases h5_1 : d 5=d 1
                ·
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_1, h3_1, h4_0, h5_1],by simp only [h2_1, h3_1, h4_0, h5_1],by simp only [h2_1, h3_1, h4_0, h5_1]⟩))))))))))
                ·
                  have h := hp (d 1)
                  simp [FibreParity, h2_1, h3_1, h4_0, h1_0, h2_0, h3_0, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h5_0, Ne.symm h5_1] at h
            ·
              by_cases h4_1 : d 4=d 1
              ·
                by_cases h5_0 : d 5=d 0
                ·
                  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_1, h3_1, h4_1, h5_0],by simp only [h2_1, h3_1, h4_1, h5_0],by simp only [h2_1, h3_1, h4_1, h5_0]⟩)))))))))))))
                ·
                  by_cases h5_1 : d 5=d 1
                  ·
                    have h := hp (d 0)
                    simp [FibreParity, h2_1, h3_1, h4_1, h5_1, h1_0, h2_0, h3_0, h4_0, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h5_0] at h
                  ·
                    have h := hp (d 0)
                    simp [FibreParity, h2_1, h3_1, h4_1, h1_0, h2_0, h3_0, h4_0, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1] at h
              ·
                by_cases h5_0 : d 5=d 0
                ·
                  have h := hp (d 1)
                  simp [FibreParity, h2_1, h3_1, h5_0, h1_0, h2_0, h3_0, h4_0, h4_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1] at h
                ·
                  by_cases h5_1 : d 5=d 1
                  ·
                    have h := hp (d 0)
                    simp [FibreParity, h2_1, h3_1, h5_1, h1_0, h2_0, h3_0, h4_0, h4_1, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0] at h
                  ·
                    by_cases h5_4 : d 5=d 4
                    ·
                      have h := hp (d 0)
                      simp [FibreParity, h2_1, h3_1, h5_4, h1_0, h2_0, h3_0, h4_0, h4_1, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1] at h
                    ·
                      have h := hp (d 0)
                      simp [FibreParity, h2_1, h3_1, h1_0, h2_0, h3_0, h4_0, h4_1, h5_0, h5_1, h5_4, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_4] at h
          ·
            by_cases h4_0 : d 4=d 0
            ·
              by_cases h5_0 : d 5=d 0
              ·
                have h := hp (d 0)
                simp [FibreParity, h2_1, h4_0, h5_0, h1_0, h2_0, h3_0, h3_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1] at h
              ·
                by_cases h5_1 : d 5=d 1
                ·
                  have h := hp (d 1)
                  simp [FibreParity, h2_1, h4_0, h5_1, h1_0, h2_0, h3_0, h3_1, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h5_0] at h
                ·
                  by_cases h5_3 : d 5=d 3
                  ·
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_1, h4_0, h5_3],by simp only [h2_1, h4_0, h5_3],by simp only [h2_1, h4_0, h5_3]⟩))))))))))
                  ·
                    have h := hp (d 3)
                    simp [FibreParity, h2_1, h4_0, h1_0, h2_0, h3_0, h3_1, h5_0, h5_1, h5_3, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_3] at h
            ·
              by_cases h4_1 : d 4=d 1
              ·
                by_cases h5_0 : d 5=d 0
                ·
                  have h := hp (d 1)
                  simp [FibreParity, h2_1, h4_1, h5_0, h1_0, h2_0, h3_0, h3_1, h4_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0] at h
                ·
                  by_cases h5_1 : d 5=d 1
                  ·
                    have h := hp (d 0)
                    simp [FibreParity, h2_1, h4_1, h5_1, h1_0, h2_0, h3_0, h3_1, h4_0, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h5_0] at h
                  ·
                    by_cases h5_3 : d 5=d 3
                    ·
                      have h := hp (d 0)
                      simp [FibreParity, h2_1, h4_1, h5_3, h1_0, h2_0, h3_0, h3_1, h4_0, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1] at h
                    ·
                      have h := hp (d 0)
                      simp [FibreParity, h2_1, h4_1, h1_0, h2_0, h3_0, h3_1, h4_0, h5_0, h5_1, h5_3, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_3] at h
              ·
                by_cases h4_3 : d 4=d 3
                ·
                  by_cases h5_0 : d 5=d 0
                  ·
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h2_1, h4_3, h5_0],by simp only [h2_1, h4_3, h5_0],by simp only [h2_1, h4_3, h5_0]⟩)))))))))))))
                  ·
                    by_cases h5_1 : d 5=d 1
                    ·
                      have h := hp (d 0)
                      simp [FibreParity, h2_1, h4_3, h5_1, h1_0, h2_0, h3_0, h3_1, h4_0, h4_1, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0] at h
                    ·
                      by_cases h5_3 : d 5=d 3
                      ·
                        have h := hp (d 0)
                        simp [FibreParity, h2_1, h4_3, h5_3, h1_0, h2_0, h3_0, h3_1, h4_0, h4_1, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1] at h
                      ·
                        have h := hp (d 0)
                        simp [FibreParity, h2_1, h4_3, h1_0, h2_0, h3_0, h3_1, h4_0, h4_1, h5_0, h5_1, h5_3, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_3] at h
                ·
                  by_cases h5_0 : d 5=d 0
                  ·
                    have h := hp (d 3)
                    simp [FibreParity, h2_1, h5_0, h1_0, h2_0, h3_0, h3_1, h4_0, h4_1, h4_3, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_3] at h
                  ·
                    by_cases h5_1 : d 5=d 1
                    ·
                      have h := hp (d 0)
                      simp [FibreParity, h2_1, h5_1, h1_0, h2_0, h3_0, h3_1, h4_0, h4_1, h4_3, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_3, Ne.symm h5_0] at h
                    ·
                      by_cases h5_3 : d 5=d 3
                      ·
                        have h := hp (d 0)
                        simp [FibreParity, h2_1, h5_3, h1_0, h2_0, h3_0, h3_1, h4_0, h4_1, h4_3, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_1] at h
                      ·
                        by_cases h5_4 : d 5=d 4
                        ·
                          have h := hp (d 0)
                          simp [FibreParity, h2_1, h5_4, h1_0, h2_0, h3_0, h3_1, h4_0, h4_1, h4_3, h5_0, h5_1, h5_3, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_3] at h
                        ·
                          have h := hp (d 0)
                          simp [FibreParity, h2_1, h1_0, h2_0, h3_0, h3_1, h4_0, h4_1, h4_3, h5_0, h5_1, h5_3, h5_4, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_3, Ne.symm h5_4] at h
      ·
        by_cases h3_0 : d 3=d 0
        ·
          by_cases h4_0 : d 4=d 0
          ·
            by_cases h5_0 : d 5=d 0
            ·
              have h := hp (d 1)
              simp [FibreParity, h3_0, h4_0, h5_0, h1_0, h2_0, h2_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1] at h
            ·
              by_cases h5_1 : d 5=d 1
              ·
                have h := hp (d 0)
                simp [FibreParity, h3_0, h4_0, h5_1, h1_0, h2_0, h2_1, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h5_0] at h
              ·
                by_cases h5_2 : d 5=d 2
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h3_0, h4_0, h5_2, h1_0, h2_0, h2_1, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h5_0, Ne.symm h5_1] at h
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h3_0, h4_0, h1_0, h2_0, h2_1, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
          ·
            by_cases h4_1 : d 4=d 1
            ·
              by_cases h5_0 : d 5=d 0
              ·
                have h := hp (d 0)
                simp [FibreParity, h3_0, h4_1, h5_0, h1_0, h2_0, h2_1, h4_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h4_0] at h
              ·
                by_cases h5_1 : d 5=d 1
                ·
                  have h := hp (d 1)
                  simp [FibreParity, h3_0, h4_1, h5_1, h1_0, h2_0, h2_1, h4_0, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h4_0, Ne.symm h5_0] at h
                ·
                  by_cases h5_2 : d 5=d 2
                  ·
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h3_0, h4_1, h5_2],by simp only [h3_0, h4_1, h5_2],by simp only [h3_0, h4_1, h5_2]⟩))))))))
                  ·
                    have h := hp (d 2)
                    simp [FibreParity, h3_0, h4_1, h1_0, h2_0, h2_1, h4_0, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
            ·
              by_cases h4_2 : d 4=d 2
              ·
                by_cases h5_0 : d 5=d 0
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h3_0, h4_2, h5_0, h1_0, h2_0, h2_1, h4_0, h4_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h4_0, Ne.symm h4_1] at h
                ·
                  by_cases h5_1 : d 5=d 1
                  ·
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h3_0, h4_2, h5_1],by simp only [h3_0, h4_2, h5_1],by simp only [h3_0, h4_2, h5_1]⟩)))))))))
                  ·
                    by_cases h5_2 : d 5=d 2
                    ·
                      have h := hp (d 1)
                      simp [FibreParity, h3_0, h4_2, h5_2, h1_0, h2_0, h2_1, h4_0, h4_1, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1] at h
                    ·
                      have h := hp (d 1)
                      simp [FibreParity, h3_0, h4_2, h1_0, h2_0, h2_1, h4_0, h4_1, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
              ·
                by_cases h5_0 : d 5=d 0
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h3_0, h5_0, h1_0, h2_0, h2_1, h4_0, h4_1, h4_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2] at h
                ·
                  by_cases h5_1 : d 5=d 1
                  ·
                    have h := hp (d 2)
                    simp [FibreParity, h3_0, h5_1, h1_0, h2_0, h2_1, h4_0, h4_1, h4_2, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0] at h
                  ·
                    by_cases h5_2 : d 5=d 2
                    ·
                      have h := hp (d 1)
                      simp [FibreParity, h3_0, h5_2, h1_0, h2_0, h2_1, h4_0, h4_1, h4_2, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_1] at h
                    ·
                      by_cases h5_4 : d 5=d 4
                      ·
                        have h := hp (d 1)
                        simp [FibreParity, h3_0, h5_4, h1_0, h2_0, h2_1, h4_0, h4_1, h4_2, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
                      ·
                        have h := hp (d 1)
                        simp [FibreParity, h3_0, h1_0, h2_0, h2_1, h4_0, h4_1, h4_2, h5_0, h5_1, h5_2, h5_4, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2, Ne.symm h5_4] at h
        ·
          by_cases h3_1 : d 3=d 1
          ·
            by_cases h4_0 : d 4=d 0
            ·
              by_cases h5_0 : d 5=d 0
              ·
                have h := hp (d 0)
                simp [FibreParity, h3_1, h4_0, h5_0, h1_0, h2_0, h2_1, h3_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0] at h
              ·
                by_cases h5_1 : d 5=d 1
                ·
                  have h := hp (d 1)
                  simp [FibreParity, h3_1, h4_0, h5_1, h1_0, h2_0, h2_1, h3_0, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h5_0] at h
                ·
                  by_cases h5_2 : d 5=d 2
                  ·
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h3_1, h4_0, h5_2],by simp only [h3_1, h4_0, h5_2],by simp only [h3_1, h4_0, h5_2]⟩)))))))))))
                  ·
                    have h := hp (d 2)
                    simp [FibreParity, h3_1, h4_0, h1_0, h2_0, h2_1, h3_0, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
            ·
              by_cases h4_1 : d 4=d 1
              ·
                by_cases h5_0 : d 5=d 0
                ·
                  have h := hp (d 1)
                  simp [FibreParity, h3_1, h4_1, h5_0, h1_0, h2_0, h2_1, h3_0, h4_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h4_0] at h
                ·
                  by_cases h5_1 : d 5=d 1
                  ·
                    have h := hp (d 0)
                    simp [FibreParity, h3_1, h4_1, h5_1, h1_0, h2_0, h2_1, h3_0, h4_0, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h5_0] at h
                  ·
                    by_cases h5_2 : d 5=d 2
                    ·
                      have h := hp (d 0)
                      simp [FibreParity, h3_1, h4_1, h5_2, h1_0, h2_0, h2_1, h3_0, h4_0, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1] at h
                    ·
                      have h := hp (d 0)
                      simp [FibreParity, h3_1, h4_1, h1_0, h2_0, h2_1, h3_0, h4_0, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
              ·
                by_cases h4_2 : d 4=d 2
                ·
                  by_cases h5_0 : d 5=d 0
                  ·
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h3_1, h4_2, h5_0],by simp only [h3_1, h4_2, h5_0],by simp only [h3_1, h4_2, h5_0]⟩))))))))))))))
                  ·
                    by_cases h5_1 : d 5=d 1
                    ·
                      have h := hp (d 0)
                      simp [FibreParity, h3_1, h4_2, h5_1, h1_0, h2_0, h2_1, h3_0, h4_0, h4_1, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0] at h
                    ·
                      by_cases h5_2 : d 5=d 2
                      ·
                        have h := hp (d 0)
                        simp [FibreParity, h3_1, h4_2, h5_2, h1_0, h2_0, h2_1, h3_0, h4_0, h4_1, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1] at h
                      ·
                        have h := hp (d 0)
                        simp [FibreParity, h3_1, h4_2, h1_0, h2_0, h2_1, h3_0, h4_0, h4_1, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
                ·
                  by_cases h5_0 : d 5=d 0
                  ·
                    have h := hp (d 2)
                    simp [FibreParity, h3_1, h5_0, h1_0, h2_0, h2_1, h3_0, h4_0, h4_1, h4_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2] at h
                  ·
                    by_cases h5_1 : d 5=d 1
                    ·
                      have h := hp (d 0)
                      simp [FibreParity, h3_1, h5_1, h1_0, h2_0, h2_1, h3_0, h4_0, h4_1, h4_2, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0] at h
                    ·
                      by_cases h5_2 : d 5=d 2
                      ·
                        have h := hp (d 0)
                        simp [FibreParity, h3_1, h5_2, h1_0, h2_0, h2_1, h3_0, h4_0, h4_1, h4_2, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_1] at h
                      ·
                        by_cases h5_4 : d 5=d 4
                        ·
                          have h := hp (d 0)
                          simp [FibreParity, h3_1, h5_4, h1_0, h2_0, h2_1, h3_0, h4_0, h4_1, h4_2, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
                        ·
                          have h := hp (d 0)
                          simp [FibreParity, h3_1, h1_0, h2_0, h2_1, h3_0, h4_0, h4_1, h4_2, h5_0, h5_1, h5_2, h5_4, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2, Ne.symm h5_4] at h
          ·
            by_cases h3_2 : d 3=d 2
            ·
              by_cases h4_0 : d 4=d 0
              ·
                by_cases h5_0 : d 5=d 0
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h3_2, h4_0, h5_0, h1_0, h2_0, h2_1, h3_0, h3_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1] at h
                ·
                  by_cases h5_1 : d 5=d 1
                  ·
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (⟨by simp only [h3_2, h4_0, h5_1],by simp only [h3_2, h4_0, h5_1],by simp only [h3_2, h4_0, h5_1]⟩))))))))))))
                  ·
                    by_cases h5_2 : d 5=d 2
                    ·
                      have h := hp (d 1)
                      simp [FibreParity, h3_2, h4_0, h5_2, h1_0, h2_0, h2_1, h3_0, h3_1, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h5_0, Ne.symm h5_1] at h
                    ·
                      have h := hp (d 1)
                      simp [FibreParity, h3_2, h4_0, h1_0, h2_0, h2_1, h3_0, h3_1, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
              ·
                by_cases h4_1 : d 4=d 1
                ·
                  by_cases h5_0 : d 5=d 0
                  ·
                    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨by simp only [h3_2, h4_1, h5_0],by simp only [h3_2, h4_1, h5_0],by simp only [h3_2, h4_1, h5_0]⟩))))))))))))))
                  ·
                    by_cases h5_1 : d 5=d 1
                    ·
                      have h := hp (d 0)
                      simp [FibreParity, h3_2, h4_1, h5_1, h1_0, h2_0, h2_1, h3_0, h3_1, h4_0, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h5_0] at h
                    ·
                      by_cases h5_2 : d 5=d 2
                      ·
                        have h := hp (d 0)
                        simp [FibreParity, h3_2, h4_1, h5_2, h1_0, h2_0, h2_1, h3_0, h3_1, h4_0, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1] at h
                      ·
                        have h := hp (d 0)
                        simp [FibreParity, h3_2, h4_1, h1_0, h2_0, h2_1, h3_0, h3_1, h4_0, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
                ·
                  by_cases h4_2 : d 4=d 2
                  ·
                    by_cases h5_0 : d 5=d 0
                    ·
                      have h := hp (d 1)
                      simp [FibreParity, h3_2, h4_2, h5_0, h1_0, h2_0, h2_1, h3_0, h3_1, h4_0, h4_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1] at h
                    ·
                      by_cases h5_1 : d 5=d 1
                      ·
                        have h := hp (d 0)
                        simp [FibreParity, h3_2, h4_2, h5_1, h1_0, h2_0, h2_1, h3_0, h3_1, h4_0, h4_1, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0] at h
                      ·
                        by_cases h5_2 : d 5=d 2
                        ·
                          have h := hp (d 0)
                          simp [FibreParity, h3_2, h4_2, h5_2, h1_0, h2_0, h2_1, h3_0, h3_1, h4_0, h4_1, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1] at h
                        ·
                          have h := hp (d 0)
                          simp [FibreParity, h3_2, h4_2, h1_0, h2_0, h2_1, h3_0, h3_1, h4_0, h4_1, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
                  ·
                    by_cases h5_0 : d 5=d 0
                    ·
                      have h := hp (d 1)
                      simp [FibreParity, h3_2, h5_0, h1_0, h2_0, h2_1, h3_0, h3_1, h4_0, h4_1, h4_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2] at h
                    ·
                      by_cases h5_1 : d 5=d 1
                      ·
                        have h := hp (d 0)
                        simp [FibreParity, h3_2, h5_1, h1_0, h2_0, h2_1, h3_0, h3_1, h4_0, h4_1, h4_2, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0] at h
                      ·
                        by_cases h5_2 : d 5=d 2
                        ·
                          have h := hp (d 0)
                          simp [FibreParity, h3_2, h5_2, h1_0, h2_0, h2_1, h3_0, h3_1, h4_0, h4_1, h4_2, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_1] at h
                        ·
                          by_cases h5_4 : d 5=d 4
                          ·
                            have h := hp (d 0)
                            simp [FibreParity, h3_2, h5_4, h1_0, h2_0, h2_1, h3_0, h3_1, h4_0, h4_1, h4_2, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
                          ·
                            have h := hp (d 0)
                            simp [FibreParity, h3_2, h1_0, h2_0, h2_1, h3_0, h3_1, h4_0, h4_1, h4_2, h5_0, h5_1, h5_2, h5_4, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2, Ne.symm h5_4] at h
            ·
              by_cases h4_0 : d 4=d 0
              ·
                by_cases h5_0 : d 5=d 0
                ·
                  have h := hp (d 0)
                  simp [FibreParity, h4_0, h5_0, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2] at h
                ·
                  by_cases h5_1 : d 5=d 1
                  ·
                    have h := hp (d 2)
                    simp [FibreParity, h4_0, h5_1, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h5_0] at h
                  ·
                    by_cases h5_2 : d 5=d 2
                    ·
                      have h := hp (d 1)
                      simp [FibreParity, h4_0, h5_2, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h5_0, Ne.symm h5_1] at h
                    ·
                      by_cases h5_3 : d 5=d 3
                      ·
                        have h := hp (d 1)
                        simp [FibreParity, h4_0, h5_3, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
                      ·
                        have h := hp (d 1)
                        simp [FibreParity, h4_0, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h5_0, h5_1, h5_2, h5_3, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2, Ne.symm h5_3] at h
              ·
                by_cases h4_1 : d 4=d 1
                ·
                  by_cases h5_0 : d 5=d 0
                  ·
                    have h := hp (d 2)
                    simp [FibreParity, h4_1, h5_0, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0] at h
                  ·
                    by_cases h5_1 : d 5=d 1
                    ·
                      have h := hp (d 0)
                      simp [FibreParity, h4_1, h5_1, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h5_0] at h
                    ·
                      by_cases h5_2 : d 5=d 2
                      ·
                        have h := hp (d 0)
                        simp [FibreParity, h4_1, h5_2, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1] at h
                      ·
                        by_cases h5_3 : d 5=d 3
                        ·
                          have h := hp (d 0)
                          simp [FibreParity, h4_1, h5_3, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
                        ·
                          have h := hp (d 0)
                          simp [FibreParity, h4_1, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h5_0, h5_1, h5_2, h5_3, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2, Ne.symm h5_3] at h
                ·
                  by_cases h4_2 : d 4=d 2
                  ·
                    by_cases h5_0 : d 5=d 0
                    ·
                      have h := hp (d 1)
                      simp [FibreParity, h4_2, h5_0, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1] at h
                    ·
                      by_cases h5_1 : d 5=d 1
                      ·
                        have h := hp (d 0)
                        simp [FibreParity, h4_2, h5_1, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0] at h
                      ·
                        by_cases h5_2 : d 5=d 2
                        ·
                          have h := hp (d 0)
                          simp [FibreParity, h4_2, h5_2, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1] at h
                        ·
                          by_cases h5_3 : d 5=d 3
                          ·
                            have h := hp (d 0)
                            simp [FibreParity, h4_2, h5_3, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
                          ·
                            have h := hp (d 0)
                            simp [FibreParity, h4_2, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h5_0, h5_1, h5_2, h5_3, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2, Ne.symm h5_3] at h
                  ·
                    by_cases h4_3 : d 4=d 3
                    ·
                      by_cases h5_0 : d 5=d 0
                      ·
                        have h := hp (d 1)
                        simp [FibreParity, h4_3, h5_0, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h4_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2] at h
                      ·
                        by_cases h5_1 : d 5=d 1
                        ·
                          have h := hp (d 0)
                          simp [FibreParity, h4_3, h5_1, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h4_2, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0] at h
                        ·
                          by_cases h5_2 : d 5=d 2
                          ·
                            have h := hp (d 0)
                            simp [FibreParity, h4_3, h5_2, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h4_2, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_1] at h
                          ·
                            by_cases h5_3 : d 5=d 3
                            ·
                              have h := hp (d 0)
                              simp [FibreParity, h4_3, h5_3, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h4_2, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
                            ·
                              have h := hp (d 0)
                              simp [FibreParity, h4_3, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h4_2, h5_0, h5_1, h5_2, h5_3, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2, Ne.symm h5_3] at h
                    ·
                      by_cases h5_0 : d 5=d 0
                      ·
                        have h := hp (d 1)
                        simp [FibreParity, h5_0, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h4_2, h4_3, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h4_3] at h
                      ·
                        by_cases h5_1 : d 5=d 1
                        ·
                          have h := hp (d 0)
                          simp [FibreParity, h5_1, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h4_2, h4_3, h5_0, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h4_3, Ne.symm h5_0] at h
                        ·
                          by_cases h5_2 : d 5=d 2
                          ·
                            have h := hp (d 0)
                            simp [FibreParity, h5_2, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h4_2, h4_3, h5_0, h5_1, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_1] at h
                          ·
                            by_cases h5_3 : d 5=d 3
                            ·
                              have h := hp (d 0)
                              simp [FibreParity, h5_3, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h4_2, h4_3, h5_0, h5_1, h5_2, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2] at h
                            ·
                              by_cases h5_4 : d 5=d 4
                              ·
                                have h := hp (d 0)
                                simp [FibreParity, h5_4, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h4_2, h4_3, h5_0, h5_1, h5_2, h5_3, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2, Ne.symm h5_3] at h
                              ·
                                have h := hp (d 0)
                                simp [FibreParity, h1_0, h2_0, h2_1, h3_0, h3_1, h3_2, h4_0, h4_1, h4_2, h4_3, h5_0, h5_1, h5_2, h5_3, h5_4, Ne.symm h1_0, Ne.symm h2_0, Ne.symm h2_1, Ne.symm h3_0, Ne.symm h3_1, Ne.symm h3_2, Ne.symm h4_0, Ne.symm h4_1, Ne.symm h4_2, Ne.symm h4_3, Ne.symm h5_0, Ne.symm h5_1, Ne.symm h5_2, Ne.symm h5_3, Ne.symm h5_4] at h
end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} [inst : DecidableEq.{p2m_u_0 + 1} α]
  (d : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → α),
  @Couret.InterIA.SingletonNecessity.FibreParity.{p2m_u_0} α inst d →
    @Couret.InterIA.SingletonNecessity.HasPairing.{p2m_u_0} α d := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_parity_has_pairing

