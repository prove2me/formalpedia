-- Prove2me | solution 1 for YogeshwaranDM.capacitated_hall_iff
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T01:53:01.016985+00:00
-- url     : https://prove2.me/submissions/0c2ce8d8-695d-4a21-9e37-b37c6926ad21

import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.SimpleGraph.Hall
import Mathlib.Tactic

set_option autoImplicit false
open scoped BigOperators

namespace YogeshwaranDM

private theorem capacitated_finset_hall {ι α : Type*} [Fintype ι] [DecidableEq α]
    (A : ι → Finset α) (d : ι → ℕ) :
    (∀ I : Finset ι, ∑ i ∈ I, d i ≤ (I.biUnion A).card) ↔
      ∃ B : ι → Finset α, (∀ i, B i ⊆ A i ∧ (B i).card = d i) ∧
        Pairwise (fun i j => Disjoint (B i) (B j)) := by
  classical
  constructor
  · intro h
    let C := (i : ι) × Fin (d i)
    let A' : C → Finset α := fun i => A i.1
    have hC (S : Finset C) : S.card ≤ (S.biUnion A').card := by
      let I : Finset ι := S.image Sigma.fst
      have hsub : S ⊆ I.sigma (fun i => Finset.univ : (i : ι) → Finset (Fin (d i))) := by
        intro i hi
        exact Finset.mem_sigma.mpr ⟨Finset.mem_image.mpr ⟨i, hi, rfl⟩, Finset.mem_univ _⟩
      have hc : S.card ≤ ∑ i ∈ I, d i := by
        have hc := Finset.card_le_card hsub
        rw [Finset.card_sigma] at hc
        simpa only [Finset.card_univ, Fintype.card_fin] using hc
      have he : I.biUnion A = S.biUnion A' := by
        ext a
        simp only [I, A', Finset.mem_biUnion, Finset.mem_image]
        aesop
      exact hc.trans (he ▸ h I)
    obtain ⟨f, hf, hfA⟩ :=
      (Finset.all_card_le_biUnion_card_iff_existsInjective' A').mp hC
    let B (i : ι) : Finset α := Finset.univ.image (fun j : Fin (d i) => f ⟨i, j⟩)
    refine ⟨B, ?_, ?_⟩
    · intro i
      constructor
      · intro a ha
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ha
        exact hfA ⟨i, j⟩
      · have hinj : Function.Injective (fun j : Fin (d i) => f ⟨i, j⟩) := by
          intro j k hjk
          exact eq_of_heq (Sigma.mk.inj_iff.mp (hf hjk) |>.2)
        simp [B, Finset.card_image_of_injective _ hinj]
    · intro i j hij
      apply Finset.disjoint_left.mpr
      intro a hai haj
      obtain ⟨u, _, hu⟩ := Finset.mem_image.mp hai
      obtain ⟨v, _, hv⟩ := Finset.mem_image.mp haj
      exact hij (congrArg Sigma.fst (hf (hu.trans hv.symm)))
  · rintro ⟨B, hB, hd⟩ I
    calc
      ∑ i ∈ I, d i = ∑ i ∈ I, (B i).card := by simp_rw [(hB _).2]
      _ = (I.biUnion B).card := (Finset.card_biUnion (fun i hi j hj hij => hd hij)).symm
      _ ≤ (I.biUnion A).card := Finset.card_le_card (by
        intro a ha
        obtain ⟨i, hi, hai⟩ := Finset.mem_biUnion.mp ha
        exact Finset.mem_biUnion.mpr ⟨i, hi, (hB i).1 hai⟩)

end YogeshwaranDM

open YogeshwaranDM

theorem solution {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [G.LocallyFinite] (L R : Set V) (hG : G.IsBipartiteWith L R)
    (hcover : L ∪ R = Set.univ) (d : L → ℕ) :
    (∃ H : G.Subgraph, (∀ x : L, (H.neighborSet x).ncard = d x) ∧
      ∀ y ∈ R, (H.neighborSet y).ncard ≤ 1) ↔
      ∀ S : Finset L, ∑ x ∈ S, d x ≤ (S.biUnion (fun x => G.neighborFinset x)).card := by
  classical
  constructor
  · rintro ⟨H, hL, hR⟩
    apply (capacitated_finset_hall (fun x : L => G.neighborFinset x) d).mpr
    let B (x : L) : Finset V := (Set.toFinite (H.neighborSet x)).toFinset
    refine ⟨B, ?_, ?_⟩
    · intro x
      constructor
      · intro y hy
        have hy' : y ∈ H.neighborSet x := by simpa only [B, Set.Finite.mem_toFinset] using hy
        exact (G.mem_neighborFinset _ _).mpr (H.adj_sub hy')
      · change (Set.toFinite (H.neighborSet x)).toFinset.card = d x
        rw [← Set.ncard_eq_toFinset_card]
        exact hL x
    · intro x z hxz
      apply Finset.disjoint_left.mpr
      intro y hxy hzy
      have hxy' : H.Adj x y := by simpa only [B, Set.Finite.mem_toFinset] using hxy
      have hzy' : H.Adj z y := by simpa only [B, Set.Finite.mem_toFinset] using hzy
      have hyR := hG.mem_of_mem_adj x.property (H.adj_sub hxy')
      have he := ((Set.ncard_le_one (s := H.neighborSet y)).mp (hR y hyR))
        x hxy'.symm z hzy'.symm
      exact hxz (Subtype.ext he)
  · intro h
    obtain ⟨B, hB, hd⟩ :=
      (capacitated_finset_hall (fun x : L => G.neighborFinset x) d).mp h
    have hadj (x : L) {y : V} (hy : y ∈ B x) : G.Adj x y :=
      (G.mem_neighborFinset _ _).mp ((hB x).1 hy)
    have hright (x : L) {y : V} (hy : y ∈ B x) : y ∈ R :=
      hG.mem_of_mem_adj x.property (hadj x hy)
    let H : G.Subgraph := {
      verts := Set.univ
      Adj := fun v w => (∃ hv : v ∈ L, w ∈ B ⟨v, hv⟩) ∨
        (∃ hw : w ∈ L, v ∈ B ⟨w, hw⟩)
      adj_sub := by
        intro v w h
        rcases h with ⟨hv, hw⟩ | ⟨hw, hv⟩
        · exact hadj ⟨v, hv⟩ hw
        · exact (hadj ⟨w, hw⟩ hv).symm
      edge_vert := by intros; trivial
      symm := by intros; tauto }
    have hleft (x : L) : H.neighborSet x = (B x : Set V) := by
      ext y
      change ((∃ hx : (x : V) ∈ L, y ∈ B ⟨x, hx⟩) ∨
        (∃ hy : y ∈ L, (x : V) ∈ B ⟨y, hy⟩)) ↔ y ∈ B x
      constructor
      · rintro (⟨hx, hy⟩ | ⟨hy, hx⟩)
        · simpa using hy
        · exact False.elim (hG.disjoint.notMem_of_mem_left x.property (hright ⟨y, hy⟩ hx))
      · intro hy
        exact Or.inl ⟨x.property, hy⟩
    have hrightAdj {y v : V} (hy : y ∈ R) (ha : H.Adj y v) :
        ∃ hv : v ∈ L, y ∈ B ⟨v, hv⟩ := by
      rcases ha with ⟨hyL, hv⟩ | hv
      · exact False.elim (hG.disjoint.notMem_of_mem_right hy hyL)
      · exact hv
    refine ⟨H, ?_, ?_⟩
    · intro x
      rw [hleft, Set.ncard_coe_finset]
      exact (hB x).2
    · intro y hy
      apply (Set.ncard_le_one (s := H.neighborSet y)).mpr
      intro v hv w hw
      obtain ⟨hvL, hyv⟩ := hrightAdj hy hv
      obtain ⟨hwL, hyw⟩ := hrightAdj hy hw
      by_contra hvw
      have hne : (⟨v, hvL⟩ : L) ≠ ⟨w, hwL⟩ := by simpa using hvw
      exact Finset.disjoint_left.mp (hd hne) hyv hyw
