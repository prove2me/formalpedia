-- Prove2me | solution 1 for mme_graded_band_part_stage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-22T16:52:46.692201+00:00
-- url     : https://prove2.me/submissions/13b0db46-b35c-46e6-bf2a-8c0f66dd01e8

import Theorems.Thm_mme_graded_integer_regional_band_step_certified_rate
import Theorems.Thm_mme_prescribed_histogram_polynomial_type_cover

open BigOperators Filter MME MME.RecursiveYZ MME.RegionRate MME.RegionRealization MME.DWZProfiledRegional
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace MME.RegionRate.BandStage

theorem histogram_reflection {P C : Type*} [Fintype P] {ell : ℕ}
    (cell : P → C) (f g : P → CompleteSplit.CompleteWord ell) (c : C)
    (h : ∀ p, cell p = c → f p = fun r ↦ Fin.rev (g p r))
    (w : CompleteSplit.CompleteWord ell) :
    count cell f c w = count cell g c (fun r ↦ Fin.rev (w r)) := by
  classical
  unfold count
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hp, hw⟩
    refine ⟨hp, ?_⟩
    funext r
    have hh := congrFun ((h p hp).symm.trans hw) r
    simpa using congrArg Fin.rev hh
  · rintro ⟨hp, hw⟩
    refine ⟨hp, ?_⟩
    rw [h p hp, hw]
    simp

/-- Histograms of supported, graded words satisfy the support and boundary-profile conditions. -/
theorem recursive_admissibility {half R ell : ℕ} {parent : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (a : Address half R parent n) (x : Fin 3 → Position n → CompleteSplit.CompleteWord ell)
    (hgrade : ∀ i, Graded htotal i a (x i))
    (hsupport : ∀ p r, (x 0 p r).val + (x 1 p r).val + (x 2 p r).val = 2) :
    BoundaryProfiles (fun i ↦ count (fullCell htotal a) (x i)) ∧
    ∀ i c w, 0 < count (fullCell htotal a) (x i) c w → ∑ h, (w h).val = (c.2.val i).val := by
  classical
  have hzero (i : Fin 3) (c : Cell half R parent) (hc : (c.2.val i).val = 0) (p : Position n)
      (hp : fullCell htotal a p = c) (r : Fin (2 ^ (ell - 1))) : (x i p r).val = 0 := by
    have hh := hgrade i p
    rw [hp, hc] at hh
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ ↦ Nat.zero_le _)).mp hh r (Finset.mem_univ r)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro c hc w
    apply histogram_reflection
    intro p hp
    funext r
    apply Fin.ext
    have hz := hzero 2 c hc p hp r
    have hs := hsupport p r
    simp only [Fin.rev, Fin.val_mk]
    omega
  · intro c hc w
    apply histogram_reflection
    intro p hp
    funext r
    apply Fin.ext
    have hz := hzero 0 c hc p hp r
    have hs := hsupport p r
    simp only [Fin.rev, Fin.val_mk]
    omega
  · intro c hc w
    apply histogram_reflection
    intro p hp
    funext r
    apply Fin.ext
    have hz := hzero 1 c hc p hp r
    have hs := hsupport p r
    simp only [Fin.rev, Fin.val_mk]
    omega
  · intro i c w hw
    have hw' : ∃ p, fullCell htotal a p = c ∧ x i p = w := by
      simpa only [count, Finset.card_pos, Finset.Nonempty, Finset.mem_filter, Finset.mem_univ,
        true_and] using hw
    obtain ⟨p, hp, hw⟩ := hw'
    have hg := hgrade i p
    rw [hp, hw] at hg
    exact hg

/-- **Band part stage.** For every `0 ≤ c` below the regional rate there is `η > 0` such that,
eventually in `t`, for every target address and every per-mode histogram condition `good` whose
histograms lie in the `η`-band of `t · mu`, the graded words with `good` histograms form the target
of a graded part stage at rate `c t`, whose types are the exact histogram triples (polynomially
many), provided the source contains the parent-graded typical band of every `good` triple. -/
theorem band_part_stage {ell R : ℕ}
    (parent : Fin R → Fin 3 → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * (2 * 2 ^ (ell - 1)))
    (n : Fin R → ℕ) (hn : ∀ r, 0 < n r) (hR : 0 < R)
    (m : ∀ r, RecursiveThinSplit.Split (2 * 2 ^ (ell - 1)) (parent r) → ℕ)
    (hm : ∀ r, ∑ c, m r c = n r)
    (mu : Fin 3 → Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < regionalRate htotal n m mu) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ t : ℕ in atTop,
      ∀ a : Address (2 * 2 ^ (ell - 1)) R parent (fun r ↦ t * n r),
        a ∈ RecursiveXHash.target (n := fun r ↦ t * n r) (fun r c ↦ t * m r c) →
      ∀ good : Fin 3 → (Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ) → Prop,
        (∀ i mu'', good i mu'' → (∀ c, ∑ w, mu'' c w = ∑ w, t * mu i c w) ∧
          ∀ c w, |(mu'' c w : ℝ) - ((t * mu i c w : ℕ) : ℝ)| ≤ η * ((∑ z, t * mu i c z : ℕ) : ℝ)) →
      ∀ S : ProfiledCW.Predicate (lenAt n t * 2 ^ (ell - 1)),
        (∀ mu' : Fin 3 → Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ,
          (∀ i, good i (mu' i)) → ∀ i x,
          ParentGraded parent (fun r ↦ t * n r) i (ProfiledCW.split (positionsAt n t) rfl x) →
          parentTypical htotal (fun r ↦ t * n r) (fun r c ↦ t * m r c) (mu' i)
            (Real.sqrt (8 * (25 * (R : ℝ) * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) *
              ((Nat.sqrt t + 2 : ℕ) : ℝ) / t))
            (ProfiledCW.split (positionsAt n t) rfl x) → S i x) →
        ∃ D : LogPartStageG (lenAt n t * 2 ^ (ell - 1)) ell S
            (fun i y ↦ Graded htotal i a (ProfiledCW.split (positionsAt n t) rfl y) ∧
              good i (count (fullCell htotal a) (ProfiledCW.split (positionsAt n t) rfl y))),
          D.types ≤ (Fintype.card (Position (fun r ↦ t * n r)) + 1) ^
            (3 * Fintype.card (Cell (2 * 2 ^ (ell - 1)) R parent) *
              Fintype.card (CompleteSplit.CompleteWord ell)) ∧
          D.rate = c * t := by
  classical
  obtain ⟨η, hη, hev⟩ := mme_graded_integer_regional_band_step_certified_rate parent htotal n hn hR
    m hm mu hmass c hc
  refine ⟨η, hη, ?_⟩
  filter_upwards [hev] with t ht
  intro a ha good hgood S hS
  let supp : (Fin 3 → Position (fun r ↦ t * n r) → CompleteSplit.CompleteWord ell) → Prop :=
    fun x ↦ ∀ p r, (x 0 p r).val + (x 1 p r).val + (x 2 p r).val = 2
  obtain ⟨types, mus, hpoly, hwit, hinside, hcover⟩ :=
    mme_prescribed_histogram_polynomial_type_cover (fullCell htotal a) supp
      (fun i f ↦ Graded htotal i a f) good
  have hstep : ∀ j, ∃ D : IntegerStepG ell (lenAt n t * 2 ^ (ell - 1)) S,
      D.step.output = (fun i x ↦ Graded htotal i a (ProfiledCW.split (positionsAt n t) rfl x) ∧
        Useful (fullCell htotal a) (mus j i) (ProfiledCW.split (positionsAt n t) rfl x)) ∧
      c * t ≤ D.step.certifiedLogCopies := by
    intro j
    obtain ⟨x, hxs, hx⟩ := hwit j
    have hadm := recursive_admissibility htotal a x (fun i ↦ (hx i).1) hxs
    have hu : (fun i ↦ count (fullCell htotal a) (x i)) = mus j :=
      funext fun i ↦ funext fun c ↦ funext fun w ↦ (hx i).2.2 c w
    have hbd : BoundaryProfiles (mus j) := by
      have := hadm.1; rw [hu] at this; exact this
    have hsp : ∀ i c w, 0 < mus j i c w → ∑ h, (w h).val = (c.2.val i).val := by
      intro i c w hw
      have hw' : 0 < count (fullCell htotal a) (x i) c w := by
        rw [show count (fullCell htotal a) (x i) = mus j i from congrFun hu i]; exact hw
      exact hadm.2 i c w hw'
    exact ht (mus j) (fun i c ↦ (hgood i _ (hx i).2.1).1 c)
      (fun i c w ↦ (hgood i _ (hx i).2.1).2 c w) hsp hbd a ha S
      (hS (mus j) (fun i ↦ (hx i).2.1))
  choose steps hout hrate using hstep
  have hin : ∀ j i x, (steps j).step.output i x →
      Graded htotal i a (ProfiledCW.split (positionsAt n t) rfl x) ∧
        good i (count (fullCell htotal a) (ProfiledCW.split (positionsAt n t) rfl x)) := by
    intro j i x hx
    rw [hout j] at hx
    exact hinside j i _ hx
  have hcov : ∀ x : Fin 3 → ProfiledCW.FineWord (lenAt n t * 2 ^ (ell - 1)), ProfiledCW.supported x →
      (∀ i, Graded htotal i a (ProfiledCW.split (positionsAt n t) rfl (x i)) ∧
        good i (count (fullCell htotal a) (ProfiledCW.split (positionsAt n t) rfl (x i)))) →
      ∃! j, ∀ i, (steps j).step.output i (x i) := by
    intro x hxs hT
    obtain ⟨j, hj, huniq⟩ := hcover (fun i ↦ ProfiledCW.split (positionsAt n t) rfl (x i))
      (fun p r ↦ hxs _) hT
    refine ⟨j, fun i ↦ ?_, fun j' hj' ↦ huniq j' (fun i ↦ ?_)⟩
    · rw [hout j]; exact hj i
    · have := hj' i; rw [hout j'] at this; exact this
  exact ⟨LogPartStageG.step types (c * t) (mul_nonneg hc0 (Nat.cast_nonneg t)) steps hrate hin hcov,
    hpoly, rfl⟩

end MME.RegionRate.BandStage

open MME.RegionRate.BandStage

theorem solution {ell R : ℕ}
    (parent : Fin R → Fin 3 → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * (2 * 2 ^ (ell - 1)))
    (n : Fin R → ℕ) (hn : ∀ r, 0 < n r) (hR : 0 < R)
    (m : ∀ r, RecursiveThinSplit.Split (2 * 2 ^ (ell - 1)) (parent r) → ℕ)
    (hm : ∀ r, ∑ c, m r c = n r)
    (mu : Fin 3 → Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ i c, ∑ w, mu i c w = m c.1 c.2 + m c.1 (complement (htotal c.1) c.2))
    (c : ℝ) (hc0 : 0 ≤ c) (hc : c < regionalRate htotal n m mu) :
    ∃ η : ℝ, 0 < η ∧ ∀ᶠ t : ℕ in atTop,
      ∀ a : Address (2 * 2 ^ (ell - 1)) R parent (fun r ↦ t * n r),
        a ∈ RecursiveXHash.target (n := fun r ↦ t * n r) (fun r c ↦ t * m r c) →
      ∀ good : Fin 3 → (Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ) → Prop,
        (∀ i mu'', good i mu'' → (∀ c, ∑ w, mu'' c w = ∑ w, t * mu i c w) ∧
          ∀ c w, |(mu'' c w : ℝ) - ((t * mu i c w : ℕ) : ℝ)| ≤ η * ((∑ z, t * mu i c z : ℕ) : ℝ)) →
      ∀ S : ProfiledCW.Predicate (lenAt n t * 2 ^ (ell - 1)),
        (∀ mu' : Fin 3 → Cell (2 * 2 ^ (ell - 1)) R parent → CompleteSplit.CompleteWord ell → ℕ,
          (∀ i, good i (mu' i)) → ∀ i x,
          ParentGraded parent (fun r ↦ t * n r) i (ProfiledCW.split (positionsAt n t) rfl x) →
          parentTypical htotal (fun r ↦ t * n r) (fun r c ↦ t * m r c) (mu' i)
            (Real.sqrt (8 * (25 * (R : ℝ) * (Fintype.card (CompleteSplit.CompleteWord ell) : ℝ) ^ 2) *
              ((Nat.sqrt t + 2 : ℕ) : ℝ) / t))
            (ProfiledCW.split (positionsAt n t) rfl x) → S i x) →
        ∃ D : LogPartStageG (lenAt n t * 2 ^ (ell - 1)) ell S
            (fun i y ↦ Graded htotal i a (ProfiledCW.split (positionsAt n t) rfl y) ∧
              good i (count (fullCell htotal a) (ProfiledCW.split (positionsAt n t) rfl y))),
          D.types ≤ (Fintype.card (Position (fun r ↦ t * n r)) + 1) ^
            (3 * Fintype.card (Cell (2 * 2 ^ (ell - 1)) R parent) *
              Fintype.card (CompleteSplit.CompleteWord ell)) ∧
          D.rate = c * t :=
  band_part_stage parent htotal n hn hR m hm mu hmass c hc0 hc

