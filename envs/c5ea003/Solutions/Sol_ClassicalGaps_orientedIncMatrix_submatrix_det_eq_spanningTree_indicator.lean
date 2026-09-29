-- Prove2me | solution 1 for ClassicalGaps.orientedIncMatrix_submatrix_det_eq_spanningTree_indicator
-- status  : ACCEPTED   (prove)
-- author  : @Rizwan G Mir
-- created : 2026-09-26T20:52:23.611986+00:00
-- url     : https://prove2.me/submissions/7d4f82ef-5266-4330-a474-816aaf4876c1

import Mathlib
import Definitions.Def_ClassicalGaps_orientedIncMatrix

open Classical Matrix ClassicalGaps

namespace KirchhoffAux


/-- Every column has entries in `{0, 1, -1}`, and any two distinct nonzero entries of a
column are negatives of each other (so each column has at most two nonzero entries). -/
def IncLike {ι κ : Type*} (N : Matrix ι κ ℝ) : Prop :=
  ∀ j, (∀ i, N i j = 0 ∨ N i j = 1 ∨ N i j = -1) ∧
    (∀ i₁ i₂, i₁ ≠ i₂ → N i₁ j ≠ 0 → N i₂ j ≠ 0 → N i₁ j + N i₂ j = 0)

lemma IncLike.submatrix {ι κ ι' κ' : Type*} {N : Matrix ι κ ℝ} (h : IncLike N)
    (f : ι' → ι) (hf : Function.Injective f) (g : κ' → κ) : IncLike (N.submatrix f g) :=
  fun j => ⟨fun i => (h (g j)).1 (f i),
    fun i₁ i₂ hne h1 h2 => (h (g j)).2 _ _ (hf.ne hne) h1 h2⟩

lemma unit_mul {x y : ℝ} (hx : x = 0 ∨ x = 1 ∨ x = -1) (hy : y = 0 ∨ y = 1 ∨ y = -1) :
    x * y = 0 ∨ x * y = 1 ∨ x * y = -1 := by
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;> norm_num

lemma det_fin : ∀ (k : ℕ) (N : Matrix (Fin k) (Fin k) ℝ), IncLike N →
    N.det = 0 ∨ N.det = 1 ∨ N.det = -1 := by
  intro k
  induction k with
  | zero => intro N _; right; left; exact Matrix.det_fin_zero
  | succ k ih =>
    intro N hN
    by_cases hA : ∃ j, ∀ i, N i j = 0
    · obtain ⟨j, hj⟩ := hA
      left; exact Matrix.det_eq_zero_of_column_eq_zero j hj
    by_cases hB : ∃ j i₀, N i₀ j ≠ 0 ∧ ∀ i, i ≠ i₀ → N i j = 0
    · obtain ⟨j, i₀, hi₀, hz⟩ := hB
      rw [Matrix.det_succ_column N j,
        Finset.sum_eq_single i₀ (fun i _ hi => by rw [hz i hi]; ring) (by simp)]
      have hm := ih (N.submatrix i₀.succAbove j.succAbove)
        (hN.submatrix i₀.succAbove (Fin.succAbove_right_injective (p := i₀)) j.succAbove)
      have hs : ((-1 : ℝ) ^ ((i₀ : ℕ) + j)) = 0 ∨ ((-1 : ℝ) ^ ((i₀ : ℕ) + j)) = 1 ∨
          ((-1 : ℝ) ^ ((i₀ : ℕ) + j)) = -1 := by
        rcases neg_one_pow_eq_or ℝ ((i₀ : ℕ) + j) with h | h <;> simp [h]
      exact unit_mul (unit_mul hs ((hN j).1 i₀)) hm
    · left
      push Not at hA hB
      rw [← Matrix.exists_vecMul_eq_zero_iff]
      refine ⟨fun _ => 1, fun h => by simpa using congrFun h 0, ?_⟩
      funext j
      simp only [Matrix.vecMul, dotProduct, one_mul, Pi.zero_apply]
      obtain ⟨i₁, h₁⟩ := hA j
      obtain ⟨i₂, hne, h₂⟩ := hB j i₁ h₁
      rw [← Finset.sum_subset (Finset.subset_univ ({i₁, i₂} : Finset (Fin (k + 1)))),
        Finset.sum_pair hne.symm]
      · exact (hN j).2 i₁ i₂ hne.symm h₁ h₂
      · intro i _ hi
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
        by_contra h
        have a := (hN j).2 i₂ i (Ne.symm hi.2) h₂ h
        have b := (hN j).2 i₁ i (Ne.symm hi.1) h₁ h
        have c := (hN j).2 i₁ i₂ hne.symm h₁ h₂
        exact h (by linarith)

lemma det_fintype {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι ℝ) (hN : IncLike N) :
    N.det = 0 ∨ N.det = 1 ∨ N.det = -1 := by
  let e := Fintype.equivFin ι
  rw [← Matrix.det_reindex_self e N]
  exact det_fin _ _ (hN.submatrix _ e.symm.injective _)


lemma entry_zero {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (s : Sym2 V) (has : a ∉ s) : orientedIncMatrix G a s = 0 := by
  unfold orientedIncMatrix
  simp only [Matrix.of_apply]
  rw [dif_neg (fun h => has h.1)]

lemma entry_cases {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a : V) (s : Sym2 V) :
    orientedIncMatrix G a s = 0 ∨ orientedIncMatrix G a s = 1 ∨ orientedIncMatrix G a s = -1 := by
  unfold orientedIncMatrix
  simp only [Matrix.of_apply]
  split_ifs <;> simp

lemma entry_ne_zero {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (a : V) (s : Sym2 V) (ha : a ∈ s) (hs : s ∈ G.edgeSet) :
    orientedIncMatrix G a s ≠ 0 := by
  unfold orientedIncMatrix
  simp only [Matrix.of_apply]
  rw [dif_pos ⟨ha, hs⟩]
  split_ifs <;> norm_num

lemma pair_sum {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u w : V) (he : s(u, w) ∈ G.edgeSet) :
    orientedIncMatrix G u s(u, w) + orientedIncMatrix G w s(u, w) = 0 := by
  have hne : u ≠ w := G.ne_of_adj (by rwa [SimpleGraph.mem_edgeSet] at he)
  have hu1 : u ∈ (s(u, w) : Sym2 V) := Sym2.mem_mk_left u w
  have hw1 : w ∈ (s(u, w) : Sym2 V) := Sym2.mem_mk_right u w
  have hother_u : Sym2.Mem.other' hu1 = w := by
    have := Sym2.other_spec' hu1
    rw [Sym2.eq_iff] at this
    rcases this with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · exact absurd h hne
  have hother_w : Sym2.Mem.other' hw1 = u := by
    have := Sym2.other_spec' hw1
    rw [Sym2.eq_iff] at this
    rcases this with ⟨h, -⟩ | ⟨-, h⟩
    · exact absurd h hne.symm
    · exact h
  unfold orientedIncMatrix
  simp only [Matrix.of_apply]
  rw [dif_pos ⟨hu1, he⟩, dif_pos ⟨hw1, he⟩, hother_u, hother_w]
  rcases lt_or_gt_of_ne (Fintype.equivFin V |>.injective.ne hne) with h | h <;>
    simp only [Fin.lt_def] at h
  · rw [if_pos h, if_neg (not_lt.mpr h.le)]; ring
  · rw [if_neg (not_lt.mpr h.le), if_pos h]; ring

theorem det_eq_zero_of_not_connected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (v₀ : V) (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset)
    (e : {x : V // x ≠ v₀} ≃ {x // x ∈ F})
    (hnc : ¬ (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Connected) :
    (Matrix.of (fun a b : {x : V // x ≠ v₀} => orientedIncMatrix G a.1 ((e b : Sym2 V)))).det = 0 := by
  set H := SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V)) with hH
  obtain ⟨x, hx⟩ : ∃ x, ¬ H.Reachable v₀ x := by
    by_contra h
    push Not at h
    haveI : Nonempty V := ⟨v₀⟩
    exact hnc (SimpleGraph.Connected.mk (fun u w => (h u).symm.trans (h w)))
  have hxv : x ≠ v₀ := by rintro rfl; exact hx (SimpleGraph.Reachable.refl _)
  -- entries vanish off the endpoints
  have hzero : ∀ (a : V) (s : Sym2 V), a ∉ s → orientedIncMatrix G a s = 0 := by
    intro a s has
    unfold orientedIncMatrix
    simp only [Matrix.of_apply]
    rw [dif_neg (fun h => has h.1)]
  -- column sums vanish
  have hsum : ∀ s ∈ G.edgeSet, ∑ v : V, orientedIncMatrix G v s = 0 := by
    intro s he
    induction s using Sym2.ind with
    | _ u w =>
    have hne : u ≠ w := G.ne_of_adj (by rwa [SimpleGraph.mem_edgeSet] at he)
    rw [← Finset.sum_subset (Finset.subset_univ ({u, w} : Finset V)) (fun y _ hy => hzero y _ (by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      rw [Sym2.mem_iff]; rintro (h | h) <;> [exact hy.1 h; exact hy.2 h])), Finset.sum_pair hne]
    have hu1 : u ∈ (s(u, w) : Sym2 V) := Sym2.mem_mk_left u w
    have hw1 : w ∈ (s(u, w) : Sym2 V) := Sym2.mem_mk_right u w
    have hother_u : Sym2.Mem.other' hu1 = w := by
      have := Sym2.other_spec' hu1
      rw [Sym2.eq_iff] at this
      rcases this with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · exact absurd h hne
    have hother_w : Sym2.Mem.other' hw1 = u := by
      have := Sym2.other_spec' hw1
      rw [Sym2.eq_iff] at this
      rcases this with ⟨h, -⟩ | ⟨-, h⟩
      · exact absurd h hne.symm
      · exact h
    unfold orientedIncMatrix
    simp only [Matrix.of_apply]
    rw [dif_pos ⟨hu1, he⟩, dif_pos ⟨hw1, he⟩, hother_u, hother_w]
    rcases lt_or_gt_of_ne (Fintype.equivFin V |>.injective.ne hne) with h | h <;>
      simp only [Fin.lt_def] at h
    · rw [if_pos h, if_neg (not_lt.mpr h.le)]; ring
    · rw [if_neg (not_lt.mpr h.le), if_pos h]; ring
  let c : {y : V // y ≠ v₀} → ℝ := fun a => if H.Reachable x a.1 then 1 else 0
  have claim : ∀ t : Sym2 V, t ∈ F →
      ∑ a : {y // y ≠ v₀}, c a * orientedIncMatrix G a.1 t = 0 := by
    intro t ht
    induction t using Sym2.ind with
    | _ p q =>
    have hG : s(p, q) ∈ G.edgeSet := by
      have := hF ht; rwa [SimpleGraph.mem_edgeFinset] at this
    have hpq : p ≠ q := G.ne_of_adj (by rwa [SimpleGraph.mem_edgeSet] at hG)
    have hadj : H.Adj p q := by
      rw [hH, SimpleGraph.fromEdgeSet_adj]; exact ⟨by simpa using ht, hpq⟩
    have hiff : ∀ a ∈ s(p, q), (H.Reachable x a ↔ H.Reachable x p) := by
      intro a ha
      rw [Sym2.mem_iff] at ha
      rcases ha with rfl | rfl
      · rfl
      · exact ⟨fun h => h.trans hadj.symm.reachable, fun h => h.trans hadj.reachable⟩
    have hterm : ∀ a : {y // y ≠ v₀}, c a * orientedIncMatrix G a.1 s(p, q) =
        if H.Reachable x p then orientedIncMatrix G a.1 s(p, q) else 0 := by
      intro a
      by_cases ha : a.1 ∈ s(p, q)
      · simp only [c, hiff a.1 ha]; split_ifs <;> simp
      · simp [hzero a.1 _ ha]
    rw [Finset.sum_congr rfl (fun a _ => hterm a)]
    split_ifs with hr
    · have hv : v₀ ∉ s(p, q) := fun hv => hx ((hiff v₀ hv).2 hr).symm
      rw [← Finset.sum_subtype (Finset.univ.erase v₀) (by simp)
        (fun v => orientedIncMatrix G v s(p, q)), Finset.sum_erase (f := fun v => orientedIncMatrix G v s(p, q)) _ (hzero v₀ _ hv)]
      exact hsum _ hG
    · simp
  rw [← Matrix.exists_vecMul_eq_zero_iff]
  refine ⟨c, ?_, ?_⟩
  · intro h
    have := congrFun h ⟨x, hxv⟩
    simp [c] at this
  · funext b
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
    exact claim _ (e b).2

theorem det_ne_zero_of_connected {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (v₀ : V) (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset)
    (e : {x : V // x ≠ v₀} ≃ {x // x ∈ F})
    (hc : (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Connected) :
    (Matrix.of (fun a b : {x : V // x ≠ v₀} => orientedIncMatrix G a.1 ((e b : Sym2 V)))).det ≠ 0 := by
  set H := SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V)) with hH
  intro hdet
  rw [← Matrix.exists_vecMul_eq_zero_iff] at hdet
  obtain ⟨c, hc0, hker⟩ := hdet
  let d : V → ℝ := fun v => if h : v = v₀ then 0 else c ⟨v, h⟩
  -- d is constant along edges of H
  have hedge : ∀ p q : V, H.Adj p q → d p = d q := by
    intro p q hpq
    rw [hH, SimpleGraph.fromEdgeSet_adj] at hpq
    obtain ⟨hmem, hne⟩ := hpq
    have hmemF : s(p, q) ∈ F := by simpa using hmem
    have hG : s(p, q) ∈ G.edgeSet := by
      have := hF hmemF; rwa [SimpleGraph.mem_edgeFinset] at this
    -- the kernel equation at the column of s(p,q)
    have hcol := congrFun hker (e.symm ⟨s(p, q), hmemF⟩)
    simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply,
      Equiv.apply_symm_apply] at hcol
    -- rewrite as a sum over all of V
    have hfull : ∑ v : V, d v * orientedIncMatrix G v s(p, q) = 0 := by
      rw [← Finset.sum_erase (f := fun v => d v * orientedIncMatrix G v s(p, q)) (a := v₀)
          Finset.univ (by simp [d]),
        Finset.sum_subtype (Finset.univ.erase v₀) (p := fun v => v ≠ v₀) (by simp)]
      rw [← hcol]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      simp [d, a.2]
    rw [← Finset.sum_subset (Finset.subset_univ ({p, q} : Finset V)) (fun y _ hy => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
      rw [entry_zero G y _ (by rw [Sym2.mem_iff]; rintro (h | h) <;> [exact hy.1 h; exact hy.2 h]),
        mul_zero]), Finset.sum_pair hne] at hfull
    have hps := pair_sum G p q hG
    have hp0 := entry_ne_zero G p _ (Sym2.mem_mk_left p q) hG
    have : (d p - d q) * orientedIncMatrix G p s(p, q) = 0 := by
      have : orientedIncMatrix G q s(p, q) = - orientedIncMatrix G p s(p, q) := by linarith
      rw [this] at hfull; linarith
    rcases mul_eq_zero.mp this with h | h
    · linarith
    · exact absurd h hp0
  have hwalk : ∀ {u w : V} (P : H.Walk u w), d u = d w := by
    intro u w P
    induction P with
    | nil => rfl
    | cons h _ ih => exact (hedge _ _ h).trans ih
  apply hc0
  funext a
  have h1 : d a.1 = d v₀ := hwalk (hc.preconnected a.1 v₀).some
  simpa [d, a.2] using h1

theorem incLike {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj]
    (v₀ : V) (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset)
    (e : {x : V // x ≠ v₀} ≃ {x // x ∈ F}) :
    IncLike (Matrix.of (fun a b : {x : V // x ≠ v₀} => orientedIncMatrix G a.1 ((e b : Sym2 V)))) := by
  intro b
  have hG : (e b : Sym2 V) ∈ G.edgeSet := by
    have := hF (e b).2; rwa [SimpleGraph.mem_edgeFinset] at this
  refine ⟨fun a => entry_cases G _ _, fun a₁ a₂ hne h1 h2 => ?_⟩
  simp only [Matrix.of_apply] at h1 h2 ⊢
  have hm1 : a₁.1 ∈ (e b : Sym2 V) := by
    by_contra h; exact h1 (entry_zero G _ _ h)
  have hm2 : a₂.1 ∈ (e b : Sym2 V) := by
    by_contra h; exact h2 (entry_zero G _ _ h)
  have hne' : a₁.1 ≠ a₂.1 := fun h => hne (Subtype.ext h)
  have hs : (e b : Sym2 V) = s(a₁.1, a₂.1) := (Sym2.mem_and_mem_iff hne').mp ⟨hm1, hm2⟩
  rw [hs] at hG ⊢
  exact pair_sum G _ _ hG

end KirchhoffAux

theorem solution
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v₀ : V) (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) (hcard : F.card + 1 = Fintype.card V)
    (e : {x : V // x ≠ v₀} ≃ {x // x ∈ F}) :
    (Matrix.of (fun a b : {x : V // x ≠ v₀} => orientedIncMatrix G a.1 ((e b : Sym2 V)))).det ^ 2 =
      (if (SimpleGraph.fromEdgeSet (↑F : Set (Sym2 V))).Connected then (1:ℝ) else 0) := by
  split_ifs with hc
  · have hne := KirchhoffAux.det_ne_zero_of_connected G v₀ F hF e hc
    rcases KirchhoffAux.det_fintype _ (KirchhoffAux.incLike G v₀ F hF e) with h | h | h
    · exact absurd h hne
    · rw [h]; norm_num
    · rw [h]; norm_num
  · rw [KirchhoffAux.det_eq_zero_of_not_connected G v₀ F hF e hc]; norm_num
