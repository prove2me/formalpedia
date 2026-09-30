-- Prove2me | solution 1 for Hirsch.affine_envelope_exposed_edge_budget
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-14T01:01:12.855691+00:00
-- url     : https://prove2.me/submissions/19eef3a9-597b-492d-a108-e2c999e1676b

import Mathlib

open Set
open scoped BigOperators
set_option autoImplicit false
noncomputable section

/-! Additive, rather than multiplicative, complexity of simultaneous affine
maximizer sweeps. Exact exposed-segment witnesses certify ordinary edges.
The general existence of such sweeps is proved in the accompanying geometric
note, not assumed to be kernel-verified by this finite certificate theorem. -/

private def slopeRank {V : Type*} [Fintype V] (b : V → ℝ) (q : V) : ℕ := by
  classical
  exact (Finset.univ.filter (fun p => b p < b q)).card

private theorem slopeRank_lt_card {V : Type*} [Fintype V]
    (b : V → ℝ) (q : V) : slopeRank b q < Fintype.card V := by
  classical
  let s := Finset.univ.filter (fun p => b p < b q)
  have hsub : s ⊂ (Finset.univ : Finset V) := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, ?_⟩
    intro he
    have hq : q ∈ s := by rw [he]; exact Finset.mem_univ q
    have hlt : b q < b q := (Finset.mem_filter.mp hq).2
    exact (lt_irrefl _) hlt
  exact Finset.card_lt_card hsub

private theorem slopeRank_mono {V : Type*} [Fintype V]
    (b : V → ℝ) (p q : V) (h : b p ≤ b q) : slopeRank b p ≤ slopeRank b q := by
  classical
  apply Finset.card_le_card
  intro v hv
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_of_lt_of_le (Finset.mem_filter.mp hv).2 h⟩

private theorem slopeRank_strict {V : Type*} [Fintype V]
    (b : V → ℝ) (p q : V) (h : b p < b q) : slopeRank b p < slopeRank b q := by
  classical
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, lt_trans (Finset.mem_filter.mp hv).2 h⟩
  · intro he
    have hp : p ∈ Finset.univ.filter (fun v => b v < b q) := by simp [h]
    rw [← he] at hp
    exact (lt_irrefl _) (Finset.mem_filter.mp hp).2

/-- A change of UNIQUE affine maximizer at increasing times strictly increases
its slope. This derives no-revisiting; it is not a certificate assumption. -/
private theorem changed_maximizer_slope {V : Type*}
    (a b : V → ℝ) (p q : V) (s t : ℝ) (hst : s < t)
    (hleft : a q + s*b q < a p + s*b p)
    (hright : a p + t*b p < a q + t*b q) : b p < b q := by
  by_contra hn
  have hb : b q ≤ b p := le_of_not_gt hn
  have hp := mul_nonneg (sub_nonneg.mpr hst.le) (sub_nonneg.mpr hb)
  nlinarith

/-- Any sequence of simultaneous affine maximizers with at least one real
change per transition has at most the SUM of the factor state budgets. -/
theorem Hirsch.affine_envelope_switch_bound
    (r N : ℕ) (k : Fin r → ℕ)
    (a b : (i : Fin r) → Fin (k i) → ℝ)
    (pick : ℕ → (i : Fin r) → Fin (k i)) (time : ℕ → ℝ)
    (hinc : ∀ j, j < N → time j < time (j+1))
    (hmax : ∀ j, j ≤ N → ∀ i q, q ≠ pick j i →
      a i q + time j*b i q < a i (pick j i) + time j*b i (pick j i))
    (hchange : ∀ j, j < N → ∃ i, pick j i ≠ pick (j+1) i) :
    N ≤ ∑ i, (k i - 1) := by
  classical
  let rank : ℕ → Fin r → ℕ := fun j i => slopeRank (b i) (pick j i)
  have hstep : ∀ j, j < N → (∑ i, rank j i) < ∑ i, rank (j+1) i := by
    intro j hj
    have hslope : ∀ i, pick j i ≠ pick (j+1) i → b i (pick j i) < b i (pick (j+1) i) := by
      intro i hi
      exact changed_maximizer_slope (a i) (b i) (pick j i) (pick (j+1) i)
        (time j) (time (j+1)) (hinc j hj)
        (hmax j (by omega) i (pick (j+1) i) (Ne.symm hi))
        (hmax (j+1) (by omega) i (pick j i) hi)
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : pick j i = pick (j+1) i
      · simp only [rank, hi]
        exact le_rfl
      · exact slopeRank_mono (b i) _ _ (hslope i hi).le
    · obtain ⟨i, hi⟩ := hchange j hj
      exact ⟨i, Finset.mem_univ _, slopeRank_strict (b i) _ _ (hslope i hi)⟩
  have hgrow : ∀ j, j ≤ N → j ≤ ∑ i, rank j i := by
    intro j
    induction j with
    | zero => intro _; exact Nat.zero_le _
    | succ j ih =>
      intro hj
      have hprev := ih (by omega)
      have hnext := hstep j (by omega)
      omega
  have htop : (∑ i, rank N i) ≤ ∑ i, (k i - 1) := by
    apply Finset.sum_le_sum
    intro i _
    have h := slopeRank_lt_card (b i) (pick N i)
    simp only [Fintype.card_fin] at h
    change slopeRank (b i) (pick N i) ≤ k i - 1
    omega
  exact (hgrow N le_rfl).trans htop

/-- Supporting slices are extreme subsets. This is the existing project's
supportFace_isExtreme argument, expressed without custom statement symbols. -/
private theorem exposed_segment_isExtreme
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (R : Set E) (f : E →ₗ[ℝ] ℝ) (β : ℝ) (x y : E)
    (hb : ∀ z ∈ R, f z ≤ β)
    (hf : {z | z ∈ R ∧ f z = β} = segment ℝ x y) :
    IsExtreme ℝ R (segment ℝ x y) := by
  rw [← hf]
  refine ⟨fun z hz => hz.1, ?_⟩
  intro p hp q hq z hz hseg
  refine ⟨hp, ?_⟩
  obtain ⟨a,c,ha,hc,hac,hcomb⟩ := hseg
  have he := congrArg f hcomb
  simp only [map_add,map_smul,smul_eq_mul] at he
  have htop : a*f p+c*f q=β := he.trans hz.2
  by_contra hn
  have hlt : f p < β := lt_of_le_of_ne (hb p hp) hn
  have h₁ := mul_lt_mul_of_pos_left hlt ha
  have h₂ := mul_le_mul_of_nonneg_left (hb q hq) hc.le
  have hscale : a*β+c*β=β := by rw [←add_mul,hac,one_mul]
  linarith

/-- Complete finite sweep certificate: genuine exposed edges and a bound
linear in the total factor dictionary size, with no no-revisit assumption. -/
theorem solution
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (R : Set E) (o : E) (r N : ℕ) (k : Fin r → ℕ)
    (v : (i : Fin r) → Fin (k i) → E)
    (f0 f1 : E →ₗ[ℝ] ℝ)
    (pick : ℕ → (i : Fin r) → Fin (k i)) (time : ℕ → ℝ)
    (wall : ℕ → E →ₗ[ℝ] ℝ) (cap : ℕ → ℝ)
    (hinc : ∀ j, j < N → time j < time (j+1))
    (hmax : ∀ j, j ≤ N → ∀ i q, q ≠ pick j i →
      f0 (v i q) + time j*f1 (v i q) <
        f0 (v i (pick j i)) + time j*f1 (v i (pick j i)))
    (hne : ∀ j, j < N →
      o + (∑ i, v i (pick j i)) ≠ o + (∑ i, v i (pick (j+1) i)))
    (hbound : ∀ j, j < N → ∀ z ∈ R, wall j z ≤ cap j)
    (hface : ∀ j, j < N →
      {z | z ∈ R ∧ wall j z = cap j} =
        segment ℝ (o + (∑ i, v i (pick j i)))
          (o + (∑ i, v i (pick (j+1) i)))) :
    N ≤ ∑ i, (k i - 1) ∧
      ∃ p : ℕ → E,
        p 0 = o + (∑ i, v i (pick 0 i)) ∧
        p N = o + (∑ i, v i (pick N i)) ∧
        ∀ j, j < N → p j ≠ p (j+1) ∧
          IsExtreme ℝ R (segment ℝ (p j) (p (j+1))) := by
  classical
  have hchange : ∀ j, j < N → ∃ i, pick j i ≠ pick (j+1) i := by
    intro j hj
    by_contra hn
    have he : ∀ i, pick j i = pick (j+1) i := by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    apply hne j hj
    congr 1
    exact Finset.sum_congr rfl (fun i _ => congrArg (v i) (he i))
  refine ⟨Hirsch.affine_envelope_switch_bound r N k
    (fun i q => f0 (v i q)) (fun i q => f1 (v i q)) pick time hinc hmax hchange,
    (fun j => o + ∑ i, v i (pick j i)), rfl, rfl, ?_⟩
  intro j hj
  exact ⟨hne j hj, exposed_segment_isExtreme R (wall j) (cap j) _ _
    (hbound j hj) (hface j hj)⟩

#print axioms Hirsch.affine_envelope_switch_bound
#print axioms exposed_segment_isExtreme
#print axioms solution
