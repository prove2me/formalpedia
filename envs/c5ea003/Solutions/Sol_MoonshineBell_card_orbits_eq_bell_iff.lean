-- Prove2me | solution 1 for MoonshineBell.card_orbits_eq_bell_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T13:43:16.474171+00:00
-- url     : https://prove2.me/submissions/f91700c6-5db0-47f6-b08d-cc2ec5d02a53

import Mathlib
import Definitions.Def_Bridges_MoonshineBellTransitivityBridge

open MoonshineBell MulAction Function in
theorem solution (k : ℕ) (G : Type*) [Group G] (X : Type*) [MulAction G X] [Finite X]
    (hk : k ≤ Nat.card X) :
    Nat.card (orbitRel.Quotient G (Fin k → X)) = bell k ↔ KTransitive k G X := by
  classical
  -- injectivity of the orbit pattern map is exactly `k`-transitivity
  have hinjiff : Injective (orbitPattern (k := k) (G := G) (X := X)) ↔ KTransitive k G X := by
    -- under `k`-transitivity, tuples with the same kernel pattern share an orbit
    have key : KTransitive k G X → ∀ f f' : Fin k → X, kerPat f = kerPat f' →
        ∃ g : G, g • f = f' := by
      intro htr f f' h
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
    constructor
    · intro hinj f f' hf hf'
      have hid : ∀ φ : Fin k → X, Injective φ → kerPat φ = id := fun φ hφ =>
        funext fun i => hφ (kerPat_apply_eq φ i)
      have hp : orbitPattern (G := G) (Quotient.mk (orbitRel G (Fin k → X)) f)
          = orbitPattern (G := G) (Quotient.mk (orbitRel G (Fin k → X)) f') :=
        Subtype.ext ((hid f hf).trans (hid f' hf').symm)
      have hrel := Quotient.exact (hinj hp)
      obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hrel
      exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
    · intro htr
      rintro ⟨f⟩ ⟨f'⟩ h
      have hk' : kerPat f = kerPat f' := congrArg Subtype.val h
      obtain ⟨g, hg⟩ := key htr f f' hk'
      apply Quotient.sound
      exact MulAction.mem_orbit_iff.2 ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  -- every pattern is realised by a tuple, since `k ≤ |X|`
  have := Fintype.ofFinite X
  have hsurj : Surjective (orbitPattern (k := k) (G := G) (X := X)) := by
    rintro ⟨p, hp_le, hp_idem⟩
    have hcard : Fintype.card (Fin k) ≤ Fintype.card X := by
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]; exact hk
    obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
    refine ⟨Quotient.mk (orbitRel G (Fin k → X)) (fun i => e (p i)), Subtype.ext ?_⟩
    show kerPat (fun i => e (p i)) = p
    funext i
    apply le_antisymm
    · exact Finset.min'_le _ _ (by simp [hp_idem i])
    · have h1 : e (p (kerPat (fun i => e (p i)) i)) = e (p i) :=
        kerPat_apply_eq (fun i => e (p i)) i
      calc p i = p (kerPat (fun i => e (p i)) i) := (e.injective h1).symm
        _ ≤ kerPat (fun i => e (p i)) i := hp_le _
  have hbell : bell k = Nat.card (Pattern k) := (Nat.card_eq_fintype_card).symm
  rw [hbell, ← hinjiff]
  constructor
  · intro h
    obtain ⟨e⟩ := Finite.card_eq.1 h
    exact (Finite.injective_iff_surjective_of_equiv e).2 hsurj
  · intro hinj
    exact Nat.card_congr (Equiv.ofBijective _ ⟨hinj, hsurj⟩)
