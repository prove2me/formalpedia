-- Prove2me | solution 2 for CartesianFootprint.footprint_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T18:56:44.358438+00:00
-- url     : https://prove2.me/submissions/0549596e-6cf1-401e-96d7-58ee2b568dbc

import Mathlib
import Definitions.Def_Bridges_CartesianFootprintBound

open MvPolynomial Polynomial Finset BigOperators Classical CartesianFootprint in
theorem solution {n : ℕ} {F : Type*} [Field F]
    (S : Fin n → Finset F)
    (hS : ∀ i, (S i).Nonempty)
    (f : MvPolynomial (Fin n) F)
    (hf : f ≠ 0)
    (e : Fin n → ℕ)
    (he : ∀ i m, m ∈ f.support → m i ≤ e i)
    (helt : ∀ i, e i < (S i).card) :
    ∏ i, ((S i).card - e i) ≤
      ((grid (F := F) S).filter (fun x => MvPolynomial.eval x f ≠ 0)).card := by
  induction n with
  | zero =>
    have hc : f = MvPolynomial.C (f.coeff 0) := f.eq_C_of_isEmpty
    have hc0 : f.coeff 0 ≠ 0 := by
      intro h
      apply hf
      rw [hc, h, map_zero]
    simp only [Finset.univ_eq_empty, Finset.prod_empty]
    apply Finset.card_pos.2
    refine ⟨fun i => i.elim0, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · unfold grid
      rw [Fintype.mem_piFinset]
      exact fun i => i.elim0
    · rw [hc, MvPolynomial.eval_C]
      exact hc0
  | succ n ih =>
    set p' : Polynomial (MvPolynomial (Fin n) F) := finSuccEquiv F n f with hp'
    set k := p'.natDegree with hk
    set pk := p'.leadingCoeff with hpk
    have hp'0 : p' ≠ 0 := EmbeddingLike.map_ne_zero_iff.2 hf
    have hpk0 : pk ≠ 0 := by simpa [pk, k]
    -- the leading coefficient obeys the same degree bounds in the remaining variables
    have hepk : ∀ i m, m ∈ pk.support → m i ≤ e i.succ := by
      intro i m hm
      have h1 : Finsupp.cons k m ∈ f.support := mem_support_coeff_finSuccEquiv.mp hm
      have h2 := he i.succ _ h1
      simpa using h2
    have hk0 : k ≤ e 0 := by
      rw [hk, hp', natDegree_finSuccEquiv]
      exact (degreeOf_le_iff).2 (fun m hm => he 0 m hm)
    have hih := ih (fun i => S i.succ) (fun i => hS i.succ) pk hpk0 (fun i => e i.succ) hepk
      (fun i => helt i.succ)
    obtain ⟨good, hgood⟩ : ∃ g : Finset (Fin n → F),
        g = (grid (F := F) (fun i => S i.succ)).filter (fun xt => MvPolynomial.eval xt pk ≠ 0) :=
      ⟨_, rfl⟩
    rw [← hgood] at hih
    -- over a good tail, the head polynomial is nonzero of degree `k ≤ e 0`
    have hhead : ∀ xt ∈ good, (S 0).card - e 0 ≤
        ((S 0).filter (fun x0 => MvPolynomial.eval (Fin.cons x0 xt) f ≠ 0)).card := by
      intro xt hxt
      rw [hgood] at hxt
      have hxt' : MvPolynomial.eval xt pk ≠ 0 := (Finset.mem_filter.1 hxt).2
      set px := p'.map (MvPolynomial.eval xt) with hpx
      have hpxdeg : px.natDegree = k := by
        rw [hpx, hk, Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ hxt']
      have hpx0 : px ≠ 0 := fun h => hxt' <| by
        rw [hpk, Polynomial.leadingCoeff, ← hk, ← hpxdeg, h, Polynomial.natDegree_zero,
          ← Polynomial.coeff_map, ← hpx, h, Polynomial.coeff_zero]
      have hz : ((S 0).filter (fun x0 => MvPolynomial.eval (Fin.cons x0 xt) f = 0)).card ≤ k := by
        calc ((S 0).filter (fun x0 => MvPolynomial.eval (Fin.cons x0 xt) f = 0)).card
            ≤ px.roots.toFinset.card := by
              apply Finset.card_le_card
              intro x0 hx0
              rw [Finset.mem_filter, eval_eq_eval_mv_eval'] at hx0
              rw [Multiset.mem_toFinset, Polynomial.mem_roots hpx0, Polynomial.IsRoot]
              exact hx0.2
          _ ≤ Multiset.card px.roots := Multiset.toFinset_card_le _
          _ ≤ px.natDegree := Polynomial.card_roots' _
          _ = k := hpxdeg
      have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
        (s := S 0) (fun x0 => MvPolynomial.eval (Fin.cons x0 xt) f = 0)
      have hne : (S 0).filter (fun x0 => ¬ MvPolynomial.eval (Fin.cons x0 xt) f = 0)
          = (S 0).filter (fun x0 => MvPolynomial.eval (Fin.cons x0 xt) f ≠ 0) := rfl
      rw [hne] at hsplit
      omega
    -- assemble head and tail choices
    have hcount : good.card * ((S 0).card - e 0) ≤
        ((grid (F := F) S).filter (fun x => MvPolynomial.eval x f ≠ 0)).card := by
      obtain ⟨T, hT⟩ : ∃ T : Finset ((Fin n → F) × F), T = (good ×ˢ S 0).filter
          (fun p => MvPolynomial.eval (Fin.cons p.2 p.1 : Fin (n + 1) → F) f ≠ 0) := ⟨_, rfl⟩
      have hTcard : good.card * ((S 0).card - e 0) ≤ T.card := by
        rw [hT, Finset.card_filter, Finset.sum_product]
        calc good.card * ((S 0).card - e 0) = ∑ xt ∈ good, ((S 0).card - e 0) := by
              rw [Finset.sum_const, smul_eq_mul]
          _ ≤ ∑ xt ∈ good, ∑ x0 ∈ S 0,
                if MvPolynomial.eval (Fin.cons x0 xt : Fin (n + 1) → F) f ≠ 0 then 1 else 0 := by
              apply Finset.sum_le_sum
              intro xt hxt
              rw [← Finset.card_filter]
              exact hhead xt hxt
      have hinj : T.card ≤ ((grid (F := F) S).filter (fun x => MvPolynomial.eval x f ≠ 0)).card := by
        apply Finset.card_le_card_of_injOn (fun p => (Fin.cons p.2 p.1 : Fin (n + 1) → F))
        · intro p hp
          rw [Finset.mem_coe, hT, Finset.mem_filter, Finset.mem_product] at hp
          rw [Finset.mem_coe, Finset.mem_filter]
          refine ⟨?_, hp.2⟩
          have hpt := hp.1.1
          rw [hgood, Finset.mem_filter] at hpt
          have hpt' := hpt.1
          unfold grid at hpt' ⊢
          rw [Fintype.mem_piFinset] at hpt' ⊢
          intro i
          refine Fin.cases ?_ (fun j => ?_) i
          · simpa using hp.1.2
          · simpa using hpt' j
        · intro p _ q _ hpq
          have h := Fin.cons_injective2 hpq
          exact Prod.ext h.2 h.1
      exact hTcard.trans hinj
    calc ∏ i, ((S i).card - e i)
        = ((S 0).card - e 0) * ∏ i : Fin n, ((S i.succ).card - e i.succ) := Fin.prod_univ_succ _
      _ ≤ ((S 0).card - e 0) * good.card := Nat.mul_le_mul_left _ hih
      _ = good.card * ((S 0).card - e 0) := mul_comm _ _
      _ ≤ _ := hcount
