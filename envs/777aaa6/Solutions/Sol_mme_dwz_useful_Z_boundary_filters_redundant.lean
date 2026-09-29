-- Prove2me | solution 1 for mme_dwz_useful_Z_boundary_filters_redundant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T15:21:48.394973+00:00
-- url     : https://prove2.me/submissions/0f735bc4-f82a-43e8-b530-6af5a8f3bc57

import Theorems.Thm_mme_basisAllAllowedSubtensor_restrict_of_coefficient_imp
import Definitions.Def_mme_dwz_simultaneous_CW_projection_data
import Theorems.Thm_mme_modern_CW_power_nonzero_coefficient_boundary_histograms

open MME Module PiTensorProduct BigOperators
open MME.TensorObj MME.CompleteSplit MME.DWZStep1Support MME.DWZSimultaneous
universe u v w
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.DWZSimultaneous

theorem tagged_fiber_card
    {A U W : Type*} [Fintype A] [Fintype U] [DecidableEq U] [DecidableEq W]
    (P : A → Prop) [DecidablePred P] (f : A → U) (tag : U → W) (w : W) :
    Fintype.card {a : A // P a ∧ tag (f a) = w} =
      ∑ u, if tag u = w then Fintype.card {a : A // P a ∧ f a = u} else 0 := by
  classical
  simp only [Fintype.card_subtype]
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := Finset.univ)
    (fun _ _ ↦ Finset.mem_univ _)]
  apply Finset.sum_congr rfl
  intro u _
  by_cases hu : tag u = w
  · rw [if_pos hu]
    congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h ↦ ⟨h.1.1, h.2⟩
    · rintro ⟨ha, hf⟩
      exact ⟨⟨ha, by simpa only [hf] using hu⟩, hf⟩
  · rw [if_neg hu]
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
    exact hu (by simpa only [ha.2] using ha.1.2)

theorem tagged_histograms_eq
    {A U W : Type*} [Fintype A] [Fintype U] [DecidableEq U] [DecidableEq W]
    (P : A → Prop) [DecidablePred P] (f g : A → U) (tag : U → W)
    (hcount : ∀ u, Fintype.card {a : A // P a ∧ f a = u} =
      Fintype.card {a : A // P a ∧ g a = u}) (w : W) :
    Fintype.card {a : A // P a ∧ tag (f a) = w} =
      Fintype.card {a : A // P a ∧ tag (g a) = w} := by
  rw [tagged_fiber_card, tagged_fiber_card]
  simp only [hcount]

theorem reflected_tagged_histograms_eq
    {A U W : Type*} [Fintype A] [Fintype U] [DecidableEq U] [DecidableEq W]
    (P : A → Prop) [DecidablePred P] (f g : A → U)
    (rev : U → U) (hrev : Function.Involutive rev)
    (tag : U → W) (flip : W → W) (hflip : Function.Involutive flip)
    (htag : ∀ u, tag (rev u) = flip (tag u))
    (hcount : ∀ u, Fintype.card {a : A // P a ∧ f a = u} =
      Fintype.card {a : A // P a ∧ g a = rev u}) (w : W) :
    Fintype.card {a : A // P a ∧ tag (f a) = w} =
      Fintype.card {a : A // P a ∧ tag (g a) = flip w} := by
  have hcount' : ∀ u, Fintype.card {a : A // P a ∧ f a = u} =
      Fintype.card {a : A // P a ∧ rev (g a) = u} := by
    intro u
    refine (hcount u).trans (Fintype.card_congr (Equiv.subtypeEquivRight ?_))
    intro a
    apply and_congr_right
    intro _
    constructor
    · intro h
      rw [h, hrev]
    · intro h
      exact (hrev (g a)).symm.trans (congrArg rev h)
  refine (tagged_histograms_eq P f (fun a ↦ rev (g a)) tag hcount' w).trans ?_
  apply Fintype.card_congr (Equiv.subtypeEquivRight _)
  intro a
  rw [htag]
  apply and_congr_right
  intro _
  constructor
  · intro h
    exact (hflip (tag (g a))).symm.trans (congrArg flip h)
  · intro h
    rw [h, hflip]

end MME.DWZSimultaneous

theorem solution
    {K : Type u} [Field K] {C : Type v} {W : Type w}
    [DecidableEq C] [DecidableEq W]
    (q ell N k : ℕ)
    (component : Fin k → Fin N → C) (shape : C → Fin 3 → ℕ)
    (tag : CompleteWord ell → W) (flip : W → W)
    (hflip : Function.Involutive flip)
    (htag : ∀ v, tag (reverseWord v) = flip (tag v))
    (mu : Fin 3 → C → W → ℕ)
    (hmuX : ∀ c, shape c 0 = 0 → ∀ w, mu 2 c w = mu 1 c (flip w))
    (hmuY : ∀ c, shape c 1 = 0 → ∀ w, mu 2 c w = mu 0 c (flip w))
    (j : Fin k) :
    TensorObj.Restrict
      ((source K q ell N).basisAllAllowedSubtensor (basis K q ell N)
        (fun i w ↦
          Graded component shape j i (label q ell N w) ∧
          (i = 2 → Profile component tag mu j 2 (label q ell N w)) ∧
          (i = 2 → ∀ j', ZCompatible component shape tag mu j' (label q ell N w) → j' = j)))
      ((source K q ell N).basisAllAllowedSubtensor (basis K q ell N)
        (fun i w ↦ Allowed component shape tag mu j i (label q ell N w))) := by
  classical
  apply mme_basisAllAllowedSubtensor_restrict_of_coefficient_imp
  intro w hcoeff hQ
  have hgrades : ∀ i, Graded component shape j i (label q ell N (w i)) :=
    fun i ↦ (hQ i).1
  have hboundary := mme_modern_CW_power_nonzero_coefficient_boundary_histograms (K := K)
    q ell N w hcoeff (component j) shape hgrades
  have hrev : Function.Involutive (@reverseWord ell) := by
    intro v
    funext r
    exact Fin.rev_rev _
  have hZ := (hQ 2).2.1 rfl
  intro i
  refine ⟨(hQ i).1, ?_, ?_, (hQ i).2.1, (hQ i).2.2⟩
  · intro hi
    subst i
    intro c hc v
    have hfull : ∀ sigma,
        Fintype.card {t : Fin N // component j t = c ∧ label q ell N (w 2) t = sigma} =
        Fintype.card {t : Fin N // component j t = c ∧
          label q ell N (w 0) t = reverseWord sigma} := by
      intro sigma
      exact hboundary.2.2 c hc sigma
    have htagged := reflected_tagged_histograms_eq (fun t ↦ component j t = c)
      (label q ell N (w 2)) (label q ell N (w 0))
      reverseWord hrev tag flip hflip htag hfull (flip v)
    calc
      Fintype.card {t : Fin N // component j t = c ∧ tag (label q ell N (w 0) t) = v} =
          Fintype.card {t : Fin N // component j t = c ∧
            tag (label q ell N (w 2) t) = flip v} := by
        simpa only [hflip v] using htagged.symm
      _ = mu 2 c (flip v) := hZ c (flip v)
      _ = mu 0 c v := by simpa only [hflip v] using hmuY c hc (flip v)
  · intro hi
    subst i
    intro c hc v
    have hfull : ∀ sigma,
        Fintype.card {t : Fin N // component j t = c ∧ label q ell N (w 2) t = sigma} =
        Fintype.card {t : Fin N // component j t = c ∧
          label q ell N (w 1) t = reverseWord sigma} := by
      intro sigma
      exact hboundary.2.1 c hc sigma
    have htagged := reflected_tagged_histograms_eq (fun t ↦ component j t = c)
      (label q ell N (w 2)) (label q ell N (w 1))
      reverseWord hrev tag flip hflip htag hfull (flip v)
    calc
      Fintype.card {t : Fin N // component j t = c ∧ tag (label q ell N (w 1) t) = v} =
          Fintype.card {t : Fin N // component j t = c ∧
            tag (label q ell N (w 2) t) = flip v} := by
        simpa only [hflip v] using htagged.symm
      _ = mu 2 c (flip v) := hZ c (flip v)
      _ = mu 1 c v := by simpa only [hflip v] using hmuX c hc (flip v)
