-- Prove2me | solution 2 for Catalog.Combinatorics.BipartiteExtremalTrees.exBip_starGraph_of_two_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T18:46:47.648417+00:00
-- url     : https://prove2.me/submissions/baff043e-7080-4a6d-b5b4-7138dc783971

import Mathlib
import Definitions.Def_Combinatorics_BipartiteExtremalTrees

open Catalog.Combinatorics.BipartiteExtremalTrees Finset Fintype SimpleGraph in
theorem solution {n k : ℕ} (h : 2 * k ≤ n) :
    exBip n (starGraph (k + 1)) = k * (n / 2) := by
  classical
  -- modular cancellation
  have hcancel : ∀ N c a b : ℕ, a < N → b < N → (c + a) % N = (c + b) % N → a = b := by
    intro N c a b ha hb hab
    have h1 : a ≡ b [MOD N] := Nat.ModEq.add_left_cancel' c hab
    rw [Nat.ModEq, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h1
    exact h1
  -- a star-free graph has maximum degree at most `k`
  have hdeg_of_free : ∀ G : SimpleGraph (Fin n), (starGraph (k + 1)).Free G →
      ∀ v, G.degree v ≤ k := by
    intro G hG v
    by_contra hlt
    have hk1 : k + 1 ≤ (G.neighborFinset v).card := by
      rw [card_neighborFinset_eq_degree]
      omega
    obtain ⟨S, hS, hScard⟩ := Finset.exists_subset_card_eq hk1
    let e : S ≃ Fin (k + 1) :=
      Fintype.equivFinOfCardEq (by rw [Fintype.card_coe]; exact hScard)
    have hSadj : ∀ x ∈ S, G.Adj v x := fun x hx => (mem_neighborFinset G v x).1 (hS hx)
    let f : Unit ⊕ Fin (k + 1) → Fin n := Sum.elim (fun _ => v) (fun i => (e.symm i : Fin n))
    have hf : ∀ a b, (starGraph (k + 1)).Adj a b → G.Adj (f a) (f b) := by
      rintro (a | a) (b | b) hab
      · simp [starGraph] at hab
      · exact hSadj _ (e.symm b).2
      · exact (hSadj _ (e.symm a).2).symm
      · simp [starGraph] at hab
    have hinj : Function.Injective f := by
      rintro (a | a) (b | b) hab
      · exact congrArg Sum.inl (Subsingleton.elim a b)
      · exfalso
        have h1 := hSadj _ (e.symm b).2
        have h2 : v = (e.symm b : Fin n) := hab
        rw [← h2] at h1
        exact G.irrefl h1
      · exfalso
        have h1 := hSadj _ (e.symm a).2
        have h2 : (e.symm a : Fin n) = v := hab
        rw [h2] at h1
        exact G.irrefl h1
      · have h2 : (e.symm a : Fin n) = (e.symm b : Fin n) := hab
        exact congrArg Sum.inr (e.symm.injective (Subtype.ext h2))
    exact hG ⟨⟨⟨f, fun hab => hf _ _ hab⟩, hinj⟩⟩
  -- conversely, maximum degree at most `k` forces star-freeness
  have hfree_of_deg : ∀ G : SimpleGraph (Fin n), (∀ v, G.degree v ≤ k) →
      (starGraph (k + 1)).Free G := by
    intro G hdeg ⟨f⟩
    have hsub : (Finset.univ.image (fun i : Fin (k + 1) => f (Sum.inr i)))
        ⊆ G.neighborFinset (f (Sum.inl ())) := by
      intro w hw
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
      rw [mem_neighborFinset]
      have hadj : (starGraph (k + 1)).Adj (Sum.inl ()) (Sum.inr i) := by simp [starGraph]
      exact f.toHom.map_adj hadj
    have hcard : (Finset.univ.image (fun i : Fin (k + 1) => f (Sum.inr i))).card = k + 1 := by
      have hinj : Function.Injective (fun i : Fin (k + 1) => f (Sum.inr i)) :=
        fun i j hij => Sum.inr_injective (f.injective hij)
      rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
    have h1 := Finset.card_le_card hsub
    rw [hcard, card_neighborFinset_eq_degree] at h1
    have h2 := hdeg (f (Sum.inl ()))
    omega
  -- upper bound: count edges from the smaller side
  have hupper : ∀ G : SimpleGraph (Fin n), (starGraph (k + 1)).Free G → G.IsBipartite →
      #G.edgeFinset ≤ k * (n / 2) := by
    intro G hF hB
    have hdeg := hdeg_of_free G hF
    obtain ⟨s, t, hst⟩ := hB.exists_isBipartiteWith
    rw [← Set.coe_toFinset s, ← Set.coe_toFinset t] at hst
    have h1 := isBipartiteWith_sum_degrees_eq_card_edges hst
    have h2 := isBipartiteWith_sum_degrees_eq_card_edges' hst
    have e1 : #G.edgeFinset ≤ #s.toFinset * k := by
      rw [← h1]
      calc ∑ v ∈ s.toFinset, G.degree v ≤ ∑ v ∈ s.toFinset, k :=
            Finset.sum_le_sum (fun v _ => hdeg v)
        _ = #s.toFinset * k := by rw [Finset.sum_const, smul_eq_mul]
    have e2 : #G.edgeFinset ≤ #t.toFinset * k := by
      rw [← h2]
      calc ∑ v ∈ t.toFinset, G.degree v ≤ ∑ v ∈ t.toFinset, k :=
            Finset.sum_le_sum (fun v _ => hdeg v)
        _ = #t.toFinset * k := by rw [Finset.sum_const, smul_eq_mul]
    have hdisj : Disjoint s.toFinset t.toFinset := Finset.disjoint_coe.1 hst.disjoint
    have hcard : #s.toFinset + #t.toFinset ≤ n := by
      have hu := Finset.card_union_add_card_inter s.toFinset t.toFinset
      rw [Finset.disjoint_iff_inter_eq_empty.1 hdisj, Finset.card_empty, add_zero] at hu
      have hle := Finset.card_le_univ (s.toFinset ∪ t.toFinset)
      rw [Fintype.card_fin] at hle
      omega
    rcases le_or_gt #s.toFinset (n / 2) with hs | hs
    · calc #G.edgeFinset ≤ #s.toFinset * k := e1
        _ ≤ (n / 2) * k := Nat.mul_le_mul_right k hs
        _ = k * (n / 2) := mul_comm _ _
    · have ht : #t.toFinset ≤ n / 2 := by omega
      calc #G.edgeFinset ≤ #t.toFinset * k := e2
        _ ≤ (n / 2) * k := Nat.mul_le_mul_right k ht
        _ = k * (n / 2) := mul_comm _ _
  -- the extremal construction: a bipartite circulant on two halves
  obtain ⟨N, hN⟩ : ∃ N, N = n / 2 := ⟨_, rfl⟩
  rw [← hN]
  have hkN : k ≤ N := by omega
  have h2N : 2 * N ≤ n := by omega
  let R : Fin n → Fin n → Prop := fun a b =>
    a.val < N ∧ N ≤ b.val ∧ b.val < 2 * N ∧ (a.val + (b.val - N)) % N < k
  let G0 : SimpleGraph (Fin n) := SimpleGraph.fromRel R
  have hG0adj : ∀ a b, G0.Adj a b ↔ a ≠ b ∧ (R a b ∨ R b a) := fun a b => SimpleGraph.fromRel_adj _ _ _
  have hG0deg : ∀ v, G0.degree v ≤ k := by
    intro v
    rw [← card_neighborFinset_eq_degree]
    by_cases hv : v.val < N
    · have hmaps : Set.MapsTo (fun w : Fin n => (v.val + (w.val - N)) % N)
          (G0.neighborFinset v) (Finset.range k) := by
        intro w hw
        rw [Finset.mem_coe, mem_neighborFinset, hG0adj] at hw
        rw [Finset.mem_coe, Finset.mem_range]
        rcases hw.2 with hr | hr
        · exact hr.2.2.2
        · exfalso
          have := hr.2.1
          omega
      have hinj : Set.InjOn (fun w : Fin n => (v.val + (w.val - N)) % N)
          (G0.neighborFinset v) := by
        intro w1 hw1 w2 hw2 heq
        rw [Finset.mem_coe, mem_neighborFinset, hG0adj] at hw1 hw2
        have r1 : R v w1 := hw1.2.resolve_right (fun hr => by have := hr.2.1; omega)
        have r2 : R v w2 := hw2.2.resolve_right (fun hr => by have := hr.2.1; omega)
        have h3 := hcancel N v.val (w1.val - N) (w2.val - N)
          (by have := r1.2.2.1; omega) (by have := r2.2.2.1; omega) heq
        apply Fin.ext
        have := r1.2.1
        have := r2.2.1
        omega
      have h4 := Finset.card_le_card_of_injOn _ hmaps hinj
      rwa [Finset.card_range] at h4
    · have hmaps : Set.MapsTo (fun w : Fin n => ((v.val - N) + w.val) % N)
          (G0.neighborFinset v) (Finset.range k) := by
        intro w hw
        rw [Finset.mem_coe, mem_neighborFinset, hG0adj] at hw
        rw [Finset.mem_coe, Finset.mem_range]
        rcases hw.2 with hr | hr
        · exfalso
          exact hv hr.1
        · show ((v.val - N) + w.val) % N < k
          rw [add_comm]
          exact hr.2.2.2
      have hinj : Set.InjOn (fun w : Fin n => ((v.val - N) + w.val) % N)
          (G0.neighborFinset v) := by
        intro w1 hw1 w2 hw2 heq
        rw [Finset.mem_coe, mem_neighborFinset, hG0adj] at hw1 hw2
        have r1 : R w1 v := hw1.2.resolve_left (fun hr => hv hr.1)
        have r2 : R w2 v := hw2.2.resolve_left (fun hr => hv hr.1)
        exact Fin.ext (hcancel N (v.val - N) w1.val w2.val r1.1 r2.1 heq)
      have h4 := Finset.card_le_card_of_injOn _ hmaps hinj
      rwa [Finset.card_range] at h4
  have hsF : G0.IsBipartiteWith ↑(univ.filter (fun v : Fin n => v.val < N))
      ↑(univ.filter (fun v : Fin n => N ≤ v.val)) := by
    constructor
    · rw [Finset.disjoint_coe, Finset.disjoint_filter]
      intro v _ h1 h2
      omega
    · intro a b hab
      rw [hG0adj] at hab
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq]
      rcases hab.2 with hr | hr
      · left
        exact ⟨hr.1, hr.2.1⟩
      · right
        exact ⟨hr.2.1, hr.1⟩
  have hleftdeg : ∀ v : Fin n, v.val < N → k ≤ G0.degree v := by
    intro v hv
    rw [← card_neighborFinset_eq_degree]
    have hNpos : 0 < N := by omega
    have hmaps : Set.MapsTo (fun d : ℕ => (⟨N + (d + (N - v.val)) % N, by
          have := Nat.mod_lt (d + (N - v.val)) hNpos
          omega⟩ : Fin n)) (Finset.range k) (G0.neighborFinset v) := by
      intro d hd
      rw [Finset.mem_coe, Finset.mem_range] at hd
      rw [Finset.mem_coe, mem_neighborFinset, hG0adj]
      have hlt := Nat.mod_lt (d + (N - v.val)) hNpos
      have key : (v.val + (d + (N - v.val)) % N) % N = d := by
        rw [Nat.add_mod_mod, show v.val + (d + (N - v.val)) = d + N by omega, Nat.add_mod_right,
          Nat.mod_eq_of_lt (by omega)]
      refine ⟨?_, Or.inl ⟨hv, ?_, ?_, ?_⟩⟩
      · intro heq
        rw [Fin.ext_iff] at heq
        simp only at heq
        omega
      · show N ≤ N + (d + (N - v.val)) % N
        omega
      · show N + (d + (N - v.val)) % N < 2 * N
        omega
      · show (v.val + (N + (d + (N - v.val)) % N - N)) % N < k
        rw [Nat.add_sub_cancel_left, key]
        exact hd
    have hinj : Set.InjOn (fun d : ℕ => (⟨N + (d + (N - v.val)) % N, by
          have := Nat.mod_lt (d + (N - v.val)) hNpos
          omega⟩ : Fin n)) (Finset.range k) := by
      intro d1 hd1 d2 hd2 heq
      rw [Finset.mem_coe, Finset.mem_range] at hd1 hd2
      rw [Fin.mk.injEq] at heq
      have h' : (d1 + (N - v.val)) % N = (d2 + (N - v.val)) % N := by omega
      rw [add_comm d1, add_comm d2] at h'
      exact hcancel N (N - v.val) d1 d2 (by omega) (by omega) h'
    have h4 := Finset.card_le_card_of_injOn _ hmaps hinj
    rwa [Finset.card_range] at h4
  have hE : k * N ≤ #G0.edgeFinset := by
    rw [← isBipartiteWith_sum_degrees_eq_card_edges hsF]
    have hcardS : N ≤ #(univ.filter (fun v : Fin n => v.val < N)) := by
      have hsub : (univ : Finset (Fin N)).image (Fin.castLE (by omega : N ≤ n))
          ⊆ univ.filter (fun v : Fin n => v.val < N) := by
        intro w hw
        obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hw
        simp [i.isLt]
      have h5 := Finset.card_le_card hsub
      rwa [Finset.card_image_of_injective _ (Fin.castLE_injective _), Finset.card_univ,
        Fintype.card_fin] at h5
    calc k * N ≤ k * #(univ.filter (fun v : Fin n => v.val < N)) := Nat.mul_le_mul_left k hcardS
      _ = ∑ v ∈ univ.filter (fun v : Fin n => v.val < N), k := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
      _ ≤ ∑ v ∈ univ.filter (fun v : Fin n => v.val < N), G0.degree v :=
          Finset.sum_le_sum (fun v hv => hleftdeg v (Finset.mem_filter.1 hv).2)
  unfold exBip
  apply le_antisymm
  · apply Finset.sup_le
    intro G hG
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hG
    have h6 := hupper G hG.1 hG.2
    rw [← hN] at h6
    exact h6
  · refine Finset.le_sup_of_le (b := G0) ?_ ?_
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hfree_of_deg G0 (fun v => by convert hG0deg v), hsF.isBipartite⟩
    · convert hE
