-- Prove2me | solution 1 for mme_global_CW_useful_mode_histogram
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T07:50:01.443499+00:00
-- url     : https://prove2.me/submissions/6a164936-24fa-4ee7-a7cb-6bb85da15881

import Definitions.Def_mme_global_CW_counting_data
import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open BigOperators MME MME.RecursiveYZ MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem count_coarsen {P C W G : Type*} [Fintype P] [Fintype C]
    (cell : P → C) (f : P → W) (group : C → G) (g : G) (w : W) :
    count (group ∘ cell) f g w = ∑ c, if group c = g then count cell f c w else 0 := by
  classical
  simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]
  have pull (c : C) :
      (if group c = g then ∑ p, if cell p = c ∧ f p = w then (1 : ℕ) else 0 else 0) =
      ∑ p, if group c = g then (if cell p = c ∧ f p = w then (1 : ℕ) else 0) else 0 := by
    by_cases h : group c = g <;> simp [h]
  simp_rw [pull]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : f p = w
  · simp only [h, and_true, Function.comp_apply]
    rw [Finset.sum_eq_single (cell p)]
    · simp
    · intro c hc hcp
      simp [Ne.symm hcp]
    · simp
  · simp [h]

private theorem fiber_card {P C W : Type*} [Fintype P]
    (cell : P → C) (f : P → W) (c : C) (w : W) :
    Fintype.card {p : {p : P // cell p = c} // f p.val = w} = count cell f c w := by
  classical
  rw [count, ← Fintype.card_coe]
  apply Fintype.card_congr
  exact {
    toFun := fun p ↦ ⟨p.val.val, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, p.val.property, p.property⟩⟩
    invFun := fun p ↦ ⟨⟨p.val, (Finset.mem_filter.mp p.property).2.1⟩,
      (Finset.mem_filter.mp p.property).2.2⟩
    left_inv := by intro p; rfl
    right_inv := by intro p; rfl }

private theorem histogram_card {P C W : Type*} [Fintype P] [Fintype C] [Fintype W]
    (cell : P → C) (mu : C → W → ℕ)
    (hsum : ∀ c, ∑ w, mu c w = Fintype.card {p : P // cell p = c}) :
    Fintype.card {f : P → W // Useful cell mu f} =
      ∏ c, (Fintype.card {p : P // cell p = c}).factorial / ∏ w, (mu c w).factorial := by
  classical
  let Family := fun c ↦ {g : {p : P // cell p = c} → W //
    ∀ w, Fintype.card {p // g p = w} = mu c w}
  have reconstruct (F : ∀ c, Family c) (c : C) :
      (fun p : {p : P // cell p = c} ↦ (F (cell p.val)).val ⟨p.val,rfl⟩) = (F c).val := by
    funext p
    obtain ⟨p,hp⟩ := p
    subst c
    rfl
  let e : {f : P → W // Useful cell mu f} ≃ (∀ c, Family c) := {
    toFun := fun f c ↦ ⟨fun p ↦ f.val p.val, by
      intro w
      rw [fiber_card]
      exact f.property c w⟩
    invFun := fun F ↦ ⟨fun p ↦ (F (cell p)).val ⟨p,rfl⟩, by
      intro c w
      rw [← fiber_card]
      have hh := congrFun (reconstruct F c)
      simp_rw [hh]
      exact (F c).property w⟩
    left_inv := by intro f; rfl
    right_inv := by
      intro F
      funext c
      apply Subtype.ext
      exact reconstruct F c }
  rw [Fintype.card_congr e, Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro c hc
  exact mme_fintype_prescribed_fiber_function_card (mu c) (hsum c)
private theorem count_region {degree R : ℕ} {n : Fin R → ℕ} {W : Type*}
    (y : ∀ r, Fin (n r) → Fin (degree+1)) (f : Place n → W)
    (r : Fin R) (j : Fin (degree+1)) (w : W) :
    count (fun p : Place n ↦ (p.1,y p.1 p.2)) f (r,j) w =
      count (y r) (fun t ↦ f ⟨r,t⟩) j w := by
  classical
  simp only [count,Finset.card_eq_sum_ones,Finset.sum_filter,Fintype.sum_sigma]
  rw [Finset.sum_eq_single r]
  · simp only [Prod.mk.injEq,true_and]
    apply Finset.sum_congr rfl
    intro t ht
    split_ifs <;> rfl
  · intro b hb hbr
    simp [Prod.mk.injEq,hbr]
  · simp

private theorem modeType_iff {degree R : ℕ} {n : Fin R → ℕ} {W : Type*}
    (y : ∀ r, Fin (n r) → Fin (degree+1))
    (eta : Fin R → Fin (degree+1) → W → ℕ) (f : Place n → W) :
    ModeType y eta f ↔ Useful (fun p : Place n ↦ (p.1,y p.1 p.2))
      (fun g : Fin R × Fin (degree+1) ↦ eta g.1 g.2) f := by
  simp only [ModeType,Useful,Prod.forall,count_region]

private theorem useful_mass {P C W : Type*} [Fintype P] [Fintype W]
    (cell : P → C) (mu : C → W → ℕ) (f : P → W) (hf : Useful cell mu f) (c : C) :
    ∑ w, mu c w = Fintype.card {p : P // cell p = c} := by
  classical
  simp_rw [← hf c]
  simp only [count,Fintype.card_subtype,Finset.card_eq_sum_ones,Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hc : cell p = c
  · simp [hc,eq_comm]
  · simp [hc]

theorem solution {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    {W : Type*} [Fintype W] (i : Fin 3) (a : RecursiveXHash.Address degree R bounds n)
    (mu : Cell degree R bounds → W → ℕ) (f : Place n → W) (hf : Useful (cell a) mu f) :
    ModeType (RecursiveXHash.block i a) (aggregate i mu) f ∧
    Nat.card {g : Place n → W // ModeType (RecursiveXHash.block i a) (aggregate i mu) g} =
      modeNumber i mu := by
  classical
  change ∀ c w, count (cell a) f c w = mu c w at hf
  have hagg : Useful (fun p : Place n ↦ (p.1,RecursiveXHash.block i a p.1 p.2))
      (fun g : Fin R × Fin (degree+1) ↦ aggregate i mu g.1 g.2) f := by
    intro g w
    change count (modeGroup i ∘ cell a) f g w = _
    rw [count_coarsen]
    simp only [aggregate,Prod.mk.eta]
    apply Finset.sum_congr rfl
    intro c hc
    split_ifs <;> simp only [hf]
  refine ⟨(modeType_iff _ _ _).mpr hagg,?_⟩
  calc
    _ = Nat.card {g : Place n → W // Useful
        (fun p : Place n ↦ (p.1,RecursiveXHash.block i a p.1 p.2))
        (fun g : Fin R × Fin (degree+1) ↦ aggregate i mu g.1 g.2) g} :=
      Nat.card_congr (Equiv.subtypeEquivRight (modeType_iff _ _))
    _ = ∏ g : Fin R × Fin (degree+1),
        (Fintype.card {p : Place n // (p.1,RecursiveXHash.block i a p.1 p.2) = g}).factorial /
          ∏ w, (aggregate i mu g.1 g.2 w).factorial := by
      simpa only [Fintype.card_eq_nat_card] using
        histogram_card _ _ (useful_mass _ _ f hagg)
    _ = modeNumber i mu := by
      unfold modeNumber histogramNumber
      apply Finset.prod_congr rfl
      intro g hg
      apply congrArg (fun z : ℕ ↦ z.factorial / ∏ w, (aggregate i mu g.1 g.2 w).factorial)
      simpa only [Fintype.card_eq_nat_card] using (useful_mass _ _ f hagg g).symm
