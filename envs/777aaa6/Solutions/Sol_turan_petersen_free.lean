-- Prove2me | solution 1 for turan_petersen_free
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:47:11.524576+00:00
-- url     : https://prove2.me/submissions/e9f8b525-c1d1-4448-b62a-e94fc60af40c

import Mathlib

set_option autoImplicit false

open SimpleGraph Filter
open scoped Topology

def petersenEdges : Finset (Nat × Nat) :=
  {(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)}

def petersenGraph : SimpleGraph (Fin 10) where
  Adj i j := (i.val, j.val) ∈ petersenEdges ∨ (j.val, i.val) ∈ petersenEdges
  symm := fun _ _ h => h.symm
  loopless := ⟨by decide⟩

instance petersenGraph.instDecidableRelAdj : DecidableRel petersenGraph.Adj := fun i j =>
  inferInstanceAs (Decidable ((i.val, j.val) ∈ petersenEdges ∨ (j.val, i.val) ∈ petersenEdges))

/-- Each vertex `m < 10` has at most three neighbours among the earlier vertices. -/
lemma petersen_card_earlier_le (m : ℕ) (hm : m < 10) :
    ((Finset.range m).filter (fun j => (j, m) ∈ petersenEdges ∨ (m, j) ∈ petersenEdges)).card ≤ 3 := by
  revert m; decide

lemma petersen_not_loop (m : ℕ) (hm : m < 10) : (m, m) ∉ petersenEdges := by
  revert m; decide

/-- Greedy embedding of the first `m` vertices of the Petersen graph into a graph on `n ≥ 40`
vertices all of whose degrees are at least `3n/4`. -/
lemma petersen_greedy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hn : 40 ≤ n)
    (hdeg : ∀ v, 3 * n ≤ 4 * G.degree v) (m : ℕ) (hm : m ≤ 10) :
    ∃ phi : ℕ → Fin n, (∀ i < m, ∀ j < m, phi i = phi j → i = j) ∧
      (∀ i < m, ∀ j < m, (i, j) ∈ petersenEdges → G.Adj (phi i) (phi j)) := by
  induction m with
  | zero =>
    refine ⟨fun _ => ⟨0, by omega⟩, ?_, ?_⟩
    · intro i hi; omega
    · intro i hi; omega
  | succ m ih =>
    obtain ⟨phi, hinj, hadj⟩ := ih (by omega)
    have hEcard := petersen_card_earlier_le m (by omega)
    set E := (Finset.range m).filter (fun j => (j, m) ∈ petersenEdges ∨ (m, j) ∈ petersenEdges) with hE
    set A := Finset.univ.filter (fun v : Fin n => ∀ j ∈ E, G.Adj (phi j) v) with hA
    have hsub : Finset.univ.filter (fun v : Fin n => ¬ ∀ j ∈ E, G.Adj (phi j) v)
        ⊆ E.biUnion (fun j => (G.neighborFinset (phi j))ᶜ) := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_forall] at hv
      obtain ⟨j, hj, hnadj⟩ := hv
      simp only [Finset.mem_biUnion, Finset.mem_compl, SimpleGraph.mem_neighborFinset]
      exact ⟨j, hj, hnadj⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_biUnion_le (s := E) (t := fun j => (G.neighborFinset (phi j))ᶜ)
    have h3 : ∀ j ∈ E, ((G.neighborFinset (phi j))ᶜ).card * 4 ≤ n := by
      intro j _
      rw [Finset.card_compl, SimpleGraph.card_neighborFinset_eq_degree, Fintype.card_fin]
      have := hdeg (phi j)
      have := G.degree_lt_card_verts (phi j)
      rw [Fintype.card_fin] at this
      omega
    have h4 : (∑ j ∈ E, ((G.neighborFinset (phi j))ᶜ).card) * 4 ≤ 3 * n := by
      rw [Finset.sum_mul]
      calc _ ≤ ∑ j ∈ E, n := Finset.sum_le_sum h3
        _ = E.card * n := by rw [Finset.sum_const, smul_eq_mul]
        _ ≤ 3 * n := Nat.mul_le_mul_right n hEcard
    have h5 := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset (Fin n))) (fun v : Fin n => ∀ j ∈ E, G.Adj (phi j) v)
    rw [Finset.card_univ, Fintype.card_fin, ← hA] at h5
    have hB : ((Finset.range m).image phi).card ≤ m := by
      calc _ ≤ (Finset.range m).card := Finset.card_image_le
        _ = m := Finset.card_range m
    have hne : (A \ (Finset.range m).image phi).Nonempty := by
      rw [← Finset.card_pos]
      have := Finset.le_card_sdiff ((Finset.range m).image phi) A
      omega
    obtain ⟨v, hv⟩ := hne
    rw [Finset.mem_sdiff, hA, Finset.mem_filter] at hv
    obtain ⟨⟨_, hvadj⟩, hvnot⟩ := hv
    refine ⟨fun i => if i = m then v else phi i, ?_, ?_⟩
    · intro i hi j hj hij
      beta_reduce at hij
      by_cases hi' : i = m <;> by_cases hj' : j = m
      · omega
      · rw [if_pos hi', if_neg hj'] at hij
        exfalso; apply hvnot
        rw [Finset.mem_image]; exact ⟨j, Finset.mem_range.mpr (by omega), hij.symm⟩
      · rw [if_neg hi', if_pos hj'] at hij
        exfalso; apply hvnot
        rw [Finset.mem_image]; exact ⟨i, Finset.mem_range.mpr (by omega), hij⟩
      · rw [if_neg hi', if_neg hj'] at hij
        exact hinj i (by omega) j (by omega) hij
    · intro i hi j hj hij
      beta_reduce
      by_cases hi' : i = m <;> by_cases hj' : j = m
      · exfalso; rw [hi', hj'] at hij; exact petersen_not_loop m (by omega) hij
      · rw [if_pos hi', if_neg hj']
        rw [hi'] at hij
        apply G.symm
        apply hvadj
        rw [hE, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, Or.inr hij⟩
      · rw [if_neg hi', if_pos hj']
        rw [hj'] at hij
        apply hvadj
        rw [hE, Finset.mem_filter, Finset.mem_range]
        exact ⟨by omega, Or.inl hij⟩
      · rw [if_neg hi', if_neg hj']
        exact hadj i (by omega) j (by omega) hij

theorem petersen_exists_degree_threshold :
    ∀ n : Nat, 40 ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      petersenGraph.Free G → (G.minDegree : ℝ) < (3 / 4 : ℝ) * n := by
  intro n hn G _ hfree
  by_contra! hdeg
  have hdeg' : 3 * n ≤ 4 * G.minDegree := by
    have : (3 : ℝ) * n ≤ 4 * G.minDegree := by linarith
    exact_mod_cast this
  have hdegv : ∀ v, 3 * n ≤ 4 * G.degree v := fun v =>
    hdeg'.trans (Nat.mul_le_mul_left 4 (G.minDegree_le_degree v))
  obtain ⟨phi, hinj, hadj⟩ := petersen_greedy G hn hdegv 10 le_rfl
  apply hfree
  refine ⟨{
    toHom := {
      toFun := fun i => phi i.val
      map_rel' := ?_ }
    injective' := ?_ }⟩
  · intro i j hij
    rcases hij with h | h
    · exact hadj i.val i.isLt j.val j.isLt h
    · exact G.symm (hadj j.val j.isLt i.val i.isLt h)
  · intro i j hij
    exact Fin.ext (hinj i.val i.isLt j.val j.isLt hij)

theorem petersen_extremal_bound (N : Nat)
    (hN : ∀ n : Nat, N ≤ n → ∀ (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      petersenGraph.Free G → (G.minDegree : ℝ) < (3 / 4 : ℝ) * n) :
    ∀ n : Nat, (extremalNumber n petersenGraph : ℝ) ≤ (3 / 8 : ℝ) * n * (n + 1) + (N : ℝ)^2 := by
  intro n
  induction n with
  | zero =>
      rw [← Fintype.card_fin 0, extremalNumber_le_iff_of_nonneg petersenGraph (by positivity)]
      intro G _ _
      have h := G.card_edgeFinset_le_card_choose_two
      simp only [Fintype.card_fin, Nat.choose_zero_succ] at h
      have hz : G.edgeFinset.card = 0 := Nat.eq_zero_of_le_zero h
      simp [hz]
  | succ n ih =>
      rw [← Fintype.card_fin (n + 1), extremalNumber_le_iff_of_nonneg petersenGraph (by positivity)]
      intro G _ hfree
      simp only [Fintype.card_fin]
      by_cases hn : N ≤ n + 1
      · obtain ⟨v, hv⟩ := G.exists_minimal_degree_vertex
        have hdeg := hN (n + 1) hn G hfree
        rw [hv] at hdeg
        have hdel := card_edgeFinset_deleteIncidenceSet_le_extremalNumber hfree v
        rw [card_edgeFinset_deleteIncidenceSet] at hdel
        simp only [Fintype.card_fin, Nat.add_sub_cancel] at hdel
        have hle := G.degree_le_card_edgeFinset v
        have hdelR' : (G.edgeFinset.card : ℝ) - G.degree v ≤ (extremalNumber n petersenGraph : ℝ) := by
          simpa only [Nat.cast_sub hle] using (show ((G.edgeFinset.card - G.degree v : Nat) : ℝ) ≤
            (extremalNumber n petersenGraph : ℝ) from by exact_mod_cast hdel)
        push_cast at *
        nlinarith
      · have hsize : (n + 1 : ℝ) ≤ N := by exact_mod_cast (le_of_lt (Nat.lt_of_not_ge hn))
        have hedge := G.card_edgeFinset_le_card_choose_two.trans (Nat.choose_le_pow _ 2)
        simp only [Fintype.card_fin] at hedge
        have hedgeR : (G.edgeFinset.card : ℝ) ≤ (n + 1 : ℝ)^2 := by
          exact_mod_cast hedge
        push_cast
        nlinarith [sq_nonneg ((N : ℝ) - (n + 1)), (Nat.cast_nonneg n : (0 : ℝ) ≤ n),
          (Nat.cast_nonneg N : (0 : ℝ) ≤ N)]

theorem solution :
    ∀ eps : ℝ, 0 < eps →
    ∃ N : ℕ, ∀ (n : ℕ) (_ : N ≤ n) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      let petersen_edges : Finset (ℕ × ℕ) :=
        {(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
          (5,7),(7,9),(9,6),(6,8),(8,5)}
      (¬∃ (phi : Fin 10 → Fin n), Function.Injective phi ∧
        ∀ i j : Fin 10, (i.val, j.val) ∈ petersen_edges → G.Adj (phi i) (phi j)) →
      (G.edgeFinset.card : ℝ) ≤ (3/4 + eps) * n * (n - 1) / 2 := by
  intro eps heps
  obtain ⟨M, hM⟩ := exists_nat_ge (6400 / eps)
  refine ⟨max M 40, fun n hn G _ hfree => ?_⟩
  have hn40 : 40 ≤ n := (le_max_right M 40).trans hn
  have hnM : (M : ℝ) ≤ n := by exact_mod_cast (le_max_left M 40).trans hn
  have hgraph : petersenGraph.Free G := by
    rintro ⟨f⟩
    apply hfree
    refine ⟨f, f.injective, fun i j hij => ?_⟩
    exact f.toHom.map_rel (Or.inl hij)
  have hb := petersen_extremal_bound 40 petersen_exists_degree_threshold n
  have he : (G.edgeFinset.card : ℝ) ≤ (extremalNumber n petersenGraph : ℝ) := by
    exact_mod_cast (show G.edgeFinset.card ≤ extremalNumber n petersenGraph from by
      simpa using card_edgeFinset_le_extremalNumber hgraph)
  have hn40R : (40 : ℝ) ≤ n := by exact_mod_cast hn40
  have h6400 : 6400 ≤ eps * n := by
    have : 6400 / eps ≤ n := hM.trans hnM
    rwa [div_le_iff₀ heps, mul_comm] at this
  have hkey := mul_le_mul_of_nonneg_right h6400 (by linarith : (0:ℝ) ≤ n - 1)
  push_cast at hb
  nlinarith

#print axioms solution
