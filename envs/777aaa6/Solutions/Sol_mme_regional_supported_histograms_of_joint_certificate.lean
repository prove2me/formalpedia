-- Prove2me | solution 1 for mme_regional_supported_histograms_of_joint_certificate
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-30T20:27:43.324943+00:00
-- url     : https://prove2.me/submissions/26668482-a485-4f79-a997-24766856ee13

import Definitions.Def_mme_recursive_yz_compatibility
import Definitions.Def_mme_graded_integer_regional_step_data
import Definitions.Def_mme_dwz_profiled_regional_positions_data
import Mathlib

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000


open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false

/-- Every integer joint histogram can be assigned to its physical cell fibers,
provided its total in each cell equals the number of physical positions. -/
theorem joint_histogram_realization {P C Z : Type*} [Fintype P] [Fintype C] [Fintype Z]
    (cell : P → C) (J : C → Z → ℕ)
    (hmass : ∀ c, ∑ z, J c z = Fintype.card {p : P // cell p = c})
    (allowed : C → Z → Prop) (hallowed : ∀ c z, 0 < J c z → allowed c z) :
    ∃ g : P → Z, (∀ p, allowed (cell p) (g p)) ∧
      ∀ c z, count cell g c z = J c z := by
  classical
  let e : ∀ c : C, {p : P // cell p = c} ≃ ((z : Z) × Fin (J c z)) := fun c ↦
    Fintype.equivOfCardEq (by simpa only [Fintype.card_sigma, Fintype.card_fin] using (hmass c).symm)
  let g : P → Z := fun p ↦ (e (cell p) ⟨p,rfl⟩).1
  have hg (c : C) (p : {p : P // cell p = c}) : g p.1 = (e c p).1 := by
    rcases p with ⟨p,hp⟩
    subst c
    rfl
  refine ⟨g, ?_, ?_⟩
  · intro p
    apply hallowed (cell p) (g p)
    have := (e (cell p) ⟨p,rfl⟩).2.isLt
    exact Nat.zero_lt_of_lt this
  · intro c z
    let f : Fin (J c z) → {p : P // cell p = c ∧ g p = z} := fun j ↦
      ⟨((e c).symm ⟨z,j⟩).1, ((e c).symm ⟨z,j⟩).2,
        by rw [hg c ((e c).symm ⟨z,j⟩), Equiv.apply_symm_apply]⟩
    have hf : Function.Bijective f := by
      constructor
      · intro i j hij
        have hvals : (f i).1 = (f j).1 :=
          congrArg (fun p : {p : P // cell p = c ∧ g p = z} ↦ p.1) hij
        have hp : (e c).symm ⟨z,i⟩ = (e c).symm ⟨z,j⟩ :=
          Subtype.ext hvals
        have hz := (e c).symm.injective hp
        simpa only [Sigma.mk.inj_iff, heq_eq_eq, true_and] using hz
      · intro p
        rcases hval : e c ⟨p.1,p.2.1⟩ with ⟨w,j⟩
        have hw : w = z := by
          have h := hg c ⟨p.1,p.2.1⟩
          rw [hval] at h
          exact h.symm.trans p.2.2
        subst w
        refine ⟨j, ?_⟩
        apply Subtype.ext
        dsimp only [f]
        have hback : (e c).symm ⟨z,j⟩ = ⟨p.1,p.2.1⟩ := by
          rw [← hval, Equiv.symm_apply_apply]
        exact congrArg Subtype.val hback
    have hcard := Fintype.card_congr (Equiv.ofBijective f hf)
    simpa only [count, Fintype.card_fin, Fintype.card_subtype, eq_comm] using hcard


private theorem count_projection_sum {P C W : Type*}
    [Fintype P] [Fintype W] (cell : P → C) (g : P → (Fin 3 → W))
    (i : Fin 3) (c : C) (w : W) :
    count cell (fun p ↦ g p i) c w =
      ∑ z ∈ Finset.univ.filter (fun z : Fin 3 → W ↦ z i = w), count cell g c z := by
  classical
  have h := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ.filter (fun p ↦ cell p = c))
    (Finset.univ.filter (fun z : Fin 3 → W ↦ z i = w)) g
  simp only [count, Finset.filter_filter, Finset.mem_filter, Finset.mem_univ,
    true_and] at h ⊢
  convert h.symm using 1
  apply Finset.sum_congr rfl
  intro z hz
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- A joint table with the prescribed three marginals supplies an actual
simultaneously supported triple of words on every physical cell fiber. -/
theorem joint_word_histograms_realization {P C W : Type*}
    [Fintype P] [Fintype C] [Fintype W]
    (cell : P → C) (J : C → (Fin 3 → W) → ℕ) (mu : Fin 3 → C → W → ℕ)
    (hmass : ∀ c, ∑ z, J c z = Fintype.card {p : P // cell p = c})
    (supported : (Fin 3 → W) → Prop) (allowed : C → Fin 3 → W → Prop)
    (hsupp : ∀ c z, 0 < J c z → supported z)
    (hallowed : ∀ c z, 0 < J c z → ∀ i, allowed c i (z i))
    (hmarg : ∀ i c w, ∑ z ∈ Finset.univ.filter (fun z : Fin 3 → W ↦ z i = w),
      J c z = mu i c w) :
    ∃ x : Fin 3 → P → W,
      (∀ p, supported (fun i ↦ x i p)) ∧
      (∀ i p, allowed (cell p) i (x i p)) ∧
      ∀ i c w, count cell (x i) c w = mu i c w := by
  classical
  obtain ⟨g, hg, hcount⟩ := joint_histogram_realization cell J hmass
    (fun c z ↦ supported z ∧ ∀ i, allowed c i (z i))
    (fun c z hz ↦ ⟨hsupp c z hz, hallowed c z hz⟩)
  refine ⟨fun i p ↦ g p i, fun p ↦ (hg p).1, fun i p ↦ (hg p).2 i, ?_⟩
  intro i c w
  rw [count_projection_sum]
  simpa only [hcount] using hmarg i c w



open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false
set_option maxHeartbeats 1600000

private theorem split_flatten {P : Type} {ell L M : ℕ}
    (positions : Fin L ≃ P) (length : L * 2 ^ (ell - 1) = M)
    (f : P → CompleteSplit.CompleteWord ell) :
    ProfiledCW.split positions length (ProfiledCW.flatten positions length f) = f := by
  funext p r
  simp [ProfiledCW.split, ProfiledCW.flatten]

private theorem supported_flatten {P : Type} {ell L M : ℕ}
    (positions : Fin L ≃ P) (length : L * 2 ^ (ell - 1) = M)
    (x : Fin 3 → P → CompleteSplit.CompleteWord ell)
    (hx : ∀ p r, (x 0 p r).val + (x 1 p r).val + (x 2 p r).val = 2) :
    ProfiledCW.supported (fun i ↦ ProfiledCW.flatten positions length (x i)) := by
  intro r
  exact hx (positions (finProdFinEquiv.symm (Fin.cast length.symm r)).1)
    (finProdFinEquiv.symm (Fin.cast length.symm r)).2

/-- A finite joint certificate gives a supported, graded flat-word triple with
the exact three prescribed regional histograms. -/
theorem solution
    {half R ell L M : ℕ} (parent : Fin R → Fin 3 → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (n : Fin R → ℕ) (a : Address half R parent n)
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (ell - 1) = M)
    (J : Cell half R parent → (Fin 3 → CompleteSplit.CompleteWord ell) → ℕ)
    (mu : Fin 3 → Cell half R parent → CompleteSplit.CompleteWord ell → ℕ)
    (hmass : ∀ c, ∑ z, J c z = Fintype.card {p : Position n // fullCell htotal a p = c})
    (hsupp : ∀ c z, 0 < J c z → ∀ r,
      (z 0 r).val + (z 1 r).val + (z 2 r).val = 2)
    (hgrade : ∀ c z, 0 < J c z → ∀ i,
      ∑ r, (z i r).val = (c.2.val i).val)
    (hmarg : ∀ i c w, ∑ z ∈ Finset.univ.filter
      (fun z : Fin 3 → CompleteSplit.CompleteWord ell ↦ z i = w), J c z = mu i c w) :
    ∃ x : Fin 3 → ProfiledCW.FineWord M, ProfiledCW.supported x ∧
      ∀ i, Graded htotal i a (ProfiledCW.split positions length (x i)) ∧
        ∀ c w, count (fullCell htotal a) (ProfiledCW.split positions length (x i)) c w =
          mu i c w := by
  classical
  obtain ⟨x, hs, hg, hc⟩ := joint_word_histograms_realization (fullCell htotal a) J mu
    (by intro c; simpa only [Fintype.card_eq_nat_card] using hmass c)
    (fun z ↦ ∀ r, (z 0 r).val + (z 1 r).val + (z 2 r).val = 2)
    (fun c i w ↦ ∑ r, (w r).val = (c.2.val i).val) hsupp hgrade (by
      intro i c w
      convert hmarg i c w using 1
      apply Finset.sum_congr
      · ext z
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      · intro z hz
        rfl)
  refine ⟨fun i ↦ ProfiledCW.flatten positions length (x i),
    supported_flatten positions length x hs, ?_⟩
  intro i
  rw [split_flatten]
  exact ⟨hg i, hc i⟩

#print axioms solution
