-- Prove2me | solution 1 for mme_global_CW_compatible_competitor_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-22T07:51:02.663038+00:00
-- url     : https://prove2.me/submissions/5d903b19-f902-426d-a008-7b85a3704af9

import Definitions.Def_mme_global_CW_counting_data
import Definitions.Def_mme_recursive_x_hash_families
import Theorems.Thm_mme_global_CW_exact_compatibility_card

open BigOperators MME MME.RecursiveYZ MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

private theorem count_perm {P C W : Type*} [Fintype P]
    (e : P ≃ P) (cell : P → C) (f : P → W) (c : C) (w : W) :
    count (cell ∘ e) (f ∘ e) c w = count cell f c w := by
  classical
  apply Finset.card_equiv e
  intro p
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]

private theorem compatible_perm {P C W G : Type*} [Fintype P] [Fintype C]
    (e : P ≃ P) (cell : P → C) (boundary : C → Prop) (group : C → G)
    (mu : C → W → ℕ) (f : P → W) :
    Compatible (cell ∘ e) boundary group mu (f ∘ e) ↔
      Compatible cell boundary group mu f := by
  classical
  simp only [Compatible, ← Function.comp_assoc, count_perm]

private theorem word_matching {half R : ℕ} {n : Fin R → ℕ} {W : Type*} [Fintype W]
    (y : ∀ r, Fin (n r) → Fin (half + 1))
    (eta : Fin R → Fin (half + 1) → W → ℕ)
    (f g : Place n → W) (hf : ModeType y eta f) (hg : ModeType y eta g) :
    ∃ sigma : ∀ r, Equiv.Perm (Fin (n r)),
      (∀ r t, y r (sigma r t) = y r t) ∧ f ∘ (Equiv.sigmaCongrRight sigma) = g := by
  classical
  have hc (r : Fin R) (v : Fin (half + 1) × W) :
      Fintype.card {t // (y r t, (fun t ↦ g ⟨r,t⟩) t) = v} =
      Fintype.card {t // (y r t, (fun t ↦ f ⟨r,t⟩) t) = v} := by
    have h := (hg r v.1 v.2).trans (hf r v.1 v.2).symm
    have hj (u : Place n → W) :
        Fintype.card {t // (y r t, (fun t ↦ u ⟨r,t⟩) t) = v} =
          count (y r) ((fun t ↦ u ⟨r,t⟩)) v.1 v.2 := by
      rw [Fintype.card_subtype]
      unfold count
      congr 1
      ext t
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.ext_iff]
    exact (hj g).trans (h.trans (hj f).symm)
  let es := fun r v ↦ Fintype.equivOfCardEq (hc r v)
  let sigma := fun r ↦ Equiv.ofFiberEquiv (es r)
  have hs (r : Fin R) (t : Fin (n r)) :
      (y r (sigma r t), (fun t ↦ f ⟨r,t⟩) (sigma r t)) = (y r t, (fun t ↦ g ⟨r,t⟩) t) :=
    Equiv.ofFiberEquiv_map (es r) t
  refine ⟨sigma, fun r t ↦ congrArg Prod.fst (hs r t), ?_⟩
  funext p
  exact congrArg Prod.snd (hs p.1 p.2)

private theorem shuffled_target {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (sigma : ∀ r, Equiv.Perm (Fin (n r))) (a : Address half R parent n) :
    shuffleAddress sigma a ∈ MME.RecursiveXHash.target m ↔
      a ∈ MME.RecursiveXHash.target m := by
  classical
  have hc (r : Fin R) (c : MME.RecursiveThinSplit.Split half (parent r)) :
      MME.RecursiveThinSplit.count ((shuffleAddress sigma a) r) c =
        MME.RecursiveThinSplit.count (a r) c := by
    apply Finset.card_equiv (sigma r)
    intro t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rfl
  simp only [MME.RecursiveXHash.target, Finset.mem_filter, Finset.mem_univ, true_and,
    MME.RecursiveThinSplit.HasJointCounts, hc]

private theorem compatible_column_constant {half R : ℕ} {parent : Fin R → Fin 3 → ℕ}
    {n : Fin R → ℕ} {W G : Type*} [Fintype W]
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (i : Fin 3) (y : ∀ r, Fin (n r) → Fin (half + 1))
    (eta : Fin R → Fin (half + 1) → W → ℕ)
    (boundary : Cell half R parent → Prop) (group : Cell half R parent → G)
    (mu : Cell half R parent → W → ℕ)
    (f g : Place n → W) (hf : ModeType y eta f) (hg : ModeType y eta g) :
    ((MME.RecursiveXHash.target (n := n) m).filter (fun a ↦
      MME.RecursiveXHash.block i a = y ∧ Compatible (cell a) boundary group mu f)).card =
    ((MME.RecursiveXHash.target (n := n) m).filter (fun a ↦
      MME.RecursiveXHash.block i a = y ∧ Compatible (cell a) boundary group mu g)).card := by
  classical
  obtain ⟨sigma, hs, hfg⟩ := word_matching y eta f g hf hg
  have hb (a : Address half R parent n) :
      MME.RecursiveXHash.block i (shuffleAddress sigma a) = y ↔
        MME.RecursiveXHash.block i a = y := by
    constructor
    · intro h
      funext r t
      have ht := congrFun (congrFun h r) ((sigma r).symm t)
      have hy := hs r ((sigma r).symm t)
      simpa [MME.RecursiveXHash.block, shuffleAddress] using ht.trans hy.symm
    · intro h
      funext r t
      exact (congrFun (congrFun h r) (sigma r t)).trans (hs r t)
  have hcell (a : Address half R parent n) :
      cell (shuffleAddress sigma a) = cell a ∘ (Equiv.sigmaCongrRight sigma) := rfl
  have hcompat (a : Address half R parent n) :
      Compatible (cell (shuffleAddress sigma a)) boundary group mu g ↔
      Compatible (cell a) boundary group mu f := by
    rw [hcell, ← hfg]
    exact compatible_perm ((Equiv.sigmaCongrRight sigma)) (cell a) boundary group mu f
  apply Finset.card_equiv (shuffleAddress sigma)
  intro a
  simp only [Finset.mem_filter, shuffled_target, hb, hcompat]

private theorem incidence_bound {A B : Type*} [DecidableEq A] [DecidableEq B]
    (S : Finset A) (F : Finset B) (rel : A → B → Prop) [DecidableRel rel]
    (f : B) (Q : ℕ)
    (hcol : ∀ g ∈ F, (S.filter (fun a ↦ rel a g)).card =
      (S.filter (fun a ↦ rel a f)).card)
    (hrow : ∀ a ∈ S, (F.filter (rel a)).card ≤ Q) :
    (S.filter (fun a ↦ rel a f)).card * F.card ≤ S.card * Q := by
  calc
    _ = ∑ g ∈ F, (S.filter (fun a ↦ rel a f)).card := by simp [Nat.mul_comm]
    _ = ∑ g ∈ F, (S.filter (fun a ↦ rel a g)).card := by
      exact Finset.sum_congr rfl (fun g hg ↦ (hcol g hg).symm)
    _ = ∑ a ∈ S, (F.filter (rel a)).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      rw [Finset.sum_comm]
    _ ≤ ∑ a ∈ S, Q := Finset.sum_le_sum hrow
    _ = _ := by simp

theorem solution {half R : ℕ} {W G : Type*} [Fintype W] [Fintype G]
    (parent : Fin R → Fin 3 → ℕ) (n : Fin R → ℕ)
    (m : ∀ r, MME.RecursiveThinSplit.Split half (parent r) → ℕ)
    (i : Fin 3) (y : ∀ r, Fin (n r) → Fin (half + 1))
    (eta : Fin R → Fin (half + 1) → W → ℕ)
    (boundary : Cell half R parent → Prop) (group : Cell half R parent → G)
    (mu : Cell half R parent → W → ℕ)
    (hmass : ∀ c, ∑ w, mu c w = m c.1 c.2)
    (f : Place n → W) (hf : ModeType y eta f) :
    ((MME.RecursiveXHash.target (n := n) m).filter (fun a ↦
        MME.RecursiveXHash.block i a = y ∧
          Compatible (cell a) boundary group mu f)).card *
        Nat.card {g : Place n → W // ModeType y eta g} ≤
      ((MME.RecursiveXHash.target (n := n) m).filter
        (fun a ↦ MME.RecursiveXHash.block i a = y)).card *
          compatibilityNumber boundary group mu := by
  classical
  let S := (MME.RecursiveXHash.target (n := n) m).filter
    (fun a ↦ MME.RecursiveXHash.block i a = y)
  let F : Finset (Place n → W) := Finset.univ.filter (ModeType y eta)
  have hc (g : Place n → W) (hg : g ∈ F) :
      (S.filter (fun a ↦ Compatible (cell a) boundary group mu g)).card =
        (S.filter (fun a ↦ Compatible (cell a) boundary group mu f)).card := by
    have hg' : ModeType y eta g := (Finset.mem_filter.mp hg).2
    simpa only [S, Finset.filter_filter] using
      compatible_column_constant m i y eta boundary group mu g f hg' hf
  have hr (a : Address half R parent n) (ha : a ∈ S) :
      (F.filter (Compatible (cell a) boundary group mu)).card ≤
        compatibilityNumber boundary group mu := by
    have hta : ∀ r, MME.RecursiveThinSplit.HasJointCounts (a r) (m r) := by
      have ha' := (Finset.mem_filter.mp ha).1
      simpa only [MME.RecursiveXHash.target, Finset.mem_filter, Finset.mem_univ,
        true_and] using ha'
    rw [← mme_global_CW_exact_compatibility_card m a (Finset.mem_filter.mp ha).1
      boundary group mu hmass, Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ F))
  have h := incidence_bound S F (fun a g ↦
    Compatible (cell a) boundary group mu g) f
      (compatibilityNumber boundary group mu) hc hr
  simpa only [S, F, Finset.filter_filter, Nat.card_eq_fintype_card,
    Fintype.card_subtype] using h
