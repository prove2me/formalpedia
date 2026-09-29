-- Prove2me | solution 1 for MoonshineBell.exists_smul_eq_of_kerPat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T02:46:57.762991+00:00
-- url     : https://prove2.me/submissions/37cf0598-16a1-413a-90a3-7be0477a97b9

import Mathlib
import Definitions.Def_Bridges_MoonshineBellTransitivityBridge

open MoonshineBell Function in
theorem solution {k : ℕ} {G : Type*} [Group G] {X : Type*} [MulAction G X] [Finite X]
    (hk : k ≤ Nat.card X) (htr : KTransitive k G X) (f f' : Fin k → X)
    (h : kerPat f = kerPat f') : ∃ g : G, g • f = f' := by
  classical
  have := Fintype.ofFinite X
  -- the representatives of the common kernel pattern
  let R : Finset (Fin k) := Finset.univ.filter (fun i => kerPat f i = i)
  -- any tuple with this pattern extends, off `R`, to an injective tuple
  have ext : ∀ φ : Fin k → X, kerPat φ = kerPat f →
      ∃ F : Fin k → X, Injective F ∧ ∀ i ∈ R, F i = φ i := by
    intro φ hφ
    have hinj : ∀ i ∈ R, ∀ j ∈ R, φ i = φ j → i = j := by
      intro i hi j hj hij
      have hi' : kerPat f i = i := (Finset.mem_filter.1 hi).2
      have hj' : kerPat f j = j := (Finset.mem_filter.1 hj).2
      have h2 := (kerPat_eq_iff φ i j).2 hij
      rw [hφ, hi', hj'] at h2
      exact h2
    have hrange : Finset.univ.image φ = R.image φ := by
      ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, rfl⟩
        refine ⟨kerPat φ i, ?_, kerPat_apply_eq φ i⟩
        simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hφ]
        exact kerPat_idem φ i
      · rintro ⟨i, -, rfl⟩
        exact ⟨i, rfl⟩
    have hcardR : (R.image φ).card = R.card :=
      Finset.card_image_of_injOn (fun i hi j hj => hinj i hi j hj)
    have hRk : R.card ≤ k := by
      simpa using Finset.card_le_univ R
    have hX : Nat.card X = Fintype.card X := Nat.card_eq_fintype_card
    have hle : Fintype.card {i // i ∉ R} ≤ Fintype.card {x // x ∉ Finset.univ.image φ} := by
      simp only [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]
      rw [hrange, hcardR]
      omega
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hle
    refine ⟨fun i => if hi : i ∈ R then φ i else (e ⟨i, hi⟩).1, ?_, ?_⟩
    · intro i j hij
      by_cases hi : i ∈ R <;> by_cases hj : j ∈ R
      · simp only [hi, hj, dif_pos] at hij
        exact hinj i hi j hj hij
      · simp only [hi, hj, dif_pos, dif_neg, not_false_eq_true] at hij
        exact absurd (hij ▸ Finset.mem_image_of_mem φ (Finset.mem_univ i)) (e ⟨j, hj⟩).2
      · simp only [hi, hj, dif_pos, dif_neg, not_false_eq_true] at hij
        exact absurd (hij.symm ▸ Finset.mem_image_of_mem φ (Finset.mem_univ j)) (e ⟨i, hi⟩).2
      · simp only [hi, hj, dif_neg, not_false_eq_true] at hij
        have h3 := e.injective (Subtype.ext hij)
        exact congrArg Subtype.val h3
    · intro i hi
      simp [hi]
  obtain ⟨F, hF, hFR⟩ := ext f rfl
  obtain ⟨F', hF', hFR'⟩ := ext f' h.symm
  obtain ⟨g, hg⟩ := htr F F' hF hF'
  refine ⟨g, funext fun i => ?_⟩
  have hrep : kerPat f i ∈ R := by
    simp only [R, Finset.mem_filter, Finset.mem_univ, true_and]
    exact kerPat_idem f i
  show g • f i = f' i
  rw [← kerPat_apply_eq f i, ← hFR _ hrep, ← kerPat_apply_eq f' i, ← h, ← hFR' _ hrep]
  exact congrFun hg _
