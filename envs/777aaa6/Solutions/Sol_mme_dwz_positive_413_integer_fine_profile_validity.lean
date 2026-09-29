-- Prove2me | solution 1 for mme_dwz_positive_413_integer_fine_profile_validity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T15:29:35.568559+00:00
-- url     : https://prove2.me/submissions/697170d4-4d91-47ba-a8e8-f3ac1fda77c8

import Definitions.Def_mme_dwz_positive_413_integer_fine_profile_data
import Definitions.Def_mme_recursive_yz_owned_filters

open BigOperators MME MME.RecursiveYZ MME.DWZ413Fine
open scoped Classical
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 1600000

namespace MME.DWZ413Fine

@[simp] theorem m_at (r : Fin 6) (j : Fin 8) :
    m r (splitEquiv r j) = weightCount r * alphaCount (region r) j * denominator := by
  simp only [m, Equiv.symm_apply_apply]

@[simp] theorem mu_at (r : Fin 6) (j : Fin 8) (i : Fin 3) (w : Fin 9) :
    mu i ⟨r,splitEquiv r j⟩ (wordEquiv w) =
      weightCount r * (alphaCount (region r) j + alphaCount (region r) (Fin.rev j)) * fineCount r j i w := by
  simp only [mu, Equiv.symm_apply_apply]

@[simp] theorem split_val (r : Fin 6) (j : Fin 8) : (splitEquiv r j).val = shape r j := rfl
@[simp] theorem word_val (w : Fin 9) : wordEquiv w = word w := rfl

@[simp] theorem complement_at (r : Fin 6) (j : Fin 8) :
    complement (parent_total r) (splitEquiv r j) = splitEquiv r (Fin.rev j) := by
  have h : ∀ r j i, parent r i - (shape r j i).val = (shape r (Fin.rev j) i).val := by decide +kernel
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact h r j i

@[simp] theorem reverse_word (w : Fin 9) :
    (fun i ↦ Fin.rev (wordEquiv w i)) = wordEquiv (Fin.rev w) := by
  have h : ∀ w, (fun i ↦ Fin.rev (word w i)) = word (Fin.rev w) := by decide +kernel
  exact h w

theorem denominator_pos : 0 < denominator := by decide

theorem alpha_mass : ∀ r, (∑ j, alphaCount r j) = 1000000000000000 := by decide +kernel

theorem fine_mass : ∀ r j i, (∑ w, fineCount r j i w) = denominator := by decide +kernel

theorem m_mass (r : Fin 6) : (∑ c, m r c) = n r := by
  rw [← (splitEquiv r).sum_comp (m r)]
  simp only [m_at, ← Finset.sum_mul, ← Finset.mul_sum, alpha_mass, n]

theorem mu_mass (i : Fin 3) (c : Cell 4 6 parent) :
    (∑ w, mu i c w) = m c.1 c.2 + m c.1 (complement (parent_total c.1) c.2) := by
  obtain ⟨r,c⟩ := c
  obtain ⟨j,rfl⟩ := (splitEquiv r).surjective c
  rw [← wordEquiv.sum_comp (mu i ⟨r,splitEquiv r j⟩)]
  simp only [mu_at, ← Finset.mul_sum, fine_mass, complement_at, m_at]
  ring

theorem mu_support (i : Fin 3) (c : Cell 4 6 parent) (w : CompleteSplit.CompleteWord 2)
    (h : 0 < mu i c w) : ∑ a, (w a).val = (c.2.val i).val := by
  obtain ⟨r,c⟩ := c
  obtain ⟨j,rfl⟩ := (splitEquiv r).surjective c
  obtain ⟨v,rfl⟩ := wordEquiv.surjective w
  rw [mu_at] at h
  have hpos : 0 < fineCount r j i v := (Nat.pos_of_mul_pos_left h)
  have hs : ∀ r j i v, 0 < fineCount r j i v →
      ∑ a, (word v a).val = (shape r j i).val := by decide +kernel
  exact hs r j i v hpos

theorem boundary_profiles : BoundaryProfiles mu := by
  have hb : ∀ r j v,
      ((shape r j 2).val = 0 → fineCount r j 1 v = fineCount r j 0 (Fin.rev v)) ∧
      ((shape r j 0).val = 0 → fineCount r j 2 v = fineCount r j 1 (Fin.rev v)) ∧
      ((shape r j 1).val = 0 → fineCount r j 2 v = fineCount r j 0 (Fin.rev v)) := by decide +kernel
  refine ⟨?_,?_,?_⟩
  all_goals
    intro c hc w
    obtain ⟨r,c⟩ := c
    obtain ⟨j,rfl⟩ := (splitEquiv r).surjective c
    obtain ⟨v,rfl⟩ := wordEquiv.surjective w
    rw [reverse_word]
    simp only [mu_at]
    congr 1
  · exact (hb r j v).1 hc
  · exact (hb r j v).2.1 hc
  · exact (hb r j v).2.2 hc

theorem retained_profile_counts : ∀ r g,
    (∑ j : Fin 8, if shape r j (keptMode r) = g then alphaCount (region r) j else 0) =
      (DWZPositiveComponent413.regionalProfile (region r)).count g := by decide +kernel

theorem retained_profile_marginal (r : Fin 6) (g : Fin 5) :
    (∑ c : RecursiveThinSplit.Split 4 (parent r), if c.val (keptMode r) = g then m r c else 0) =
      weightCount r * (DWZPositiveComponent413.regionalProfile (region r)).count g * denominator := by
  rw [← (splitEquiv r).sum_comp]
  simp only [split_val, m_at]
  have hid : (∑ j : Fin 8, if shape r j (keptMode r) = g then weightCount r * alphaCount (region r) j * denominator else 0) =
      weightCount r * (∑ j : Fin 8, if shape r j (keptMode r) = g then alphaCount (region r) j else 0) * denominator := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul, mul_zero, zero_mul]
  rw [hid]
  rw [retained_profile_counts]

theorem original_profile_mixture : ∀ g : Fin 5,
    (∑ r : Fin 6, weightCount r * (DWZPositiveComponent413.regionalProfile (region r)).count g) =
      2 * DWZPositiveComponent413.parentProfile.count g := by decide +kernel

theorem n_positive : ∀ r, 0 < n r := by decide +kernel

theorem n_sum : (∑ r, n r) = totalCount := by decide +kernel

end MME.DWZ413Fine

theorem solution :
    (∀ r, (∑ c, m r c) = n r) ∧
    (∀ i c, (∑ w, mu i c w) = m c.1 c.2 + m c.1 (complement (parent_total c.1) c.2)) ∧
    (∀ i c w, 0 < mu i c w → ∑ a, (w a).val = (c.2.val i).val) ∧
    BoundaryProfiles mu ∧
    (∀ r g, (∑ c : RecursiveThinSplit.Split 4 (parent r), if c.val (keptMode r) = g then m r c else 0) =
      weightCount r * (DWZPositiveComponent413.regionalProfile (region r)).count g * denominator) ∧
    (∀ g, (∑ r, weightCount r * (DWZPositiveComponent413.regionalProfile (region r)).count g) =
      2 * DWZPositiveComponent413.parentProfile.count g) ∧
    (∀ r, 0 < n r) ∧ (∑ r, n r) = totalCount := by
  exact ⟨m_mass, mu_mass, mu_support, boundary_profiles, retained_profile_marginal,
    original_profile_mixture, n_positive, n_sum⟩
