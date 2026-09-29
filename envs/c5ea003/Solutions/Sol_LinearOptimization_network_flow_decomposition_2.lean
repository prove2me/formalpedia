-- Prove2me | solution 2 for LinearOptimization.network_flow_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-06T21:03:48.875283+00:00
-- url     : https://prove2.me/submissions/d7a48ec7-56ad-4cd5-adec-db8f5ec448ce

import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_LinearOptimization_NetworkFlowProblem
import Theorems.Thm_LinearOptimization_positive_directed_cycle_of_circulation
import Theorems.Thm_LinearOptimization_traversalVector_isCirculation_of_isCycle

/-!
# Flow decomposition (Bertsimas & Tsitsiklis, Lemma 7.1, p. 298)

A nonnegative circulation is a positive combination of simple circulations of
directed cycles; if the circulation is integer, the coefficients can be taken
to be positive integers.

The proof is the book's: peel off one directed cycle in the support at a time,
subtracting the largest multiple that keeps the flow nonnegative — this zeroes
at least one more arc, so the support strictly shrinks.
-/

open Matrix

namespace FlowDecomp

open LinearOptimization

variable {n m : ℕ} {arcs : Fin m → Fin n × Fin n}

/-- The support of a flow vector. -/
noncomputable def supp (f : Fin m → ℝ) : Finset (Fin m) := by
  classical
  exact Finset.univ.filter (fun e => f e ≠ 0)

lemma mem_supp {f : Fin m → ℝ} {e : Fin m} : e ∈ supp f ↔ f e ≠ 0 := by
  classical
  simp [supp]

/-- The main induction: peel directed cycles off the support. -/
lemma decompose (hloop : HasNoSelfLoops arcs) :
    ∀ (N : ℕ) (f : Fin m → ℝ), (supp f).card ≤ N → 0 ≤ f → IsCirculation arcs f →
      ∃ (k : ℕ) (cyc : Fin k → List (Fin m × Bool)) (a : Fin k → ℝ),
        (∀ i, ∃ v, IsCycle arcs v (cyc i)) ∧
        (∀ i, ∀ st ∈ cyc i, st.2 = true) ∧
        (∀ i, 0 < a i) ∧
        (f = fun e => ∑ i, a i * traversalVector (cyc i) e) ∧
        ((∀ e, ∃ z : ℤ, f e = (z : ℝ)) → ∀ i, ∃ z : ℤ, a i = (z : ℝ)) := by
  classical
  intro N
  induction N with
  | zero =>
      intro f hcard _ _
      have hzero : f = 0 := by
        funext e
        by_contra hne
        have : e ∈ supp f := mem_supp.2 hne
        have : 0 < (supp f).card := Finset.card_pos.2 ⟨e, this⟩
        omega
      exact ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, by rw [hzero]; funext e; simp, fun _ i => i.elim0⟩
  | succ N ih =>
      intro f hcard hnn hcirc
      by_cases hzero : f = 0
      · exact ⟨0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0,
          fun i => i.elim0, by rw [hzero]; funext e; simp, fun _ i => i.elim0⟩
      obtain ⟨v, C, hcyc, hfwd, hpos⟩ :=
        LinearOptimization.positive_directed_cycle_of_circulation arcs hloop f hnn hcirc hzero
      -- the traversal vector of an all-forward cycle is a 0/1 indicator
      have htvfalse : ∀ e : Fin m, (e, false) ∉ C := by
        intro e he
        simpa using hfwd _ he
      have htv : ∀ e : Fin m, traversalVector C e = if (e, true) ∈ C then 1 else 0 := by
        intro e
        simp [traversalVector, htvfalse e]
      -- the arcs used by the cycle
      set S : Finset (Fin m) := (C.map Prod.fst).toFinset with hS
      have hmemS : ∀ e : Fin m, e ∈ S ↔ (e, true) ∈ C := by
        intro e
        simp only [hS, List.mem_toFinset, List.mem_map]
        constructor
        · rintro ⟨st, hst, hfst⟩
          have : st = (e, true) := Prod.ext_iff.2 ⟨hfst, hfwd st hst⟩
          rwa [this] at hst
        · intro h; exact ⟨(e, true), h, rfl⟩
      have hSne : S.Nonempty := by
        obtain ⟨st, hst⟩ := List.exists_mem_of_ne_nil C hcyc.1
        exact ⟨st.1, by simp only [hS, List.mem_toFinset, List.mem_map]; exact ⟨st, hst, rfl⟩⟩
      have hSpos : ∀ e ∈ S, 0 < f e := by
        intro e he
        exact hpos (e, true) ((hmemS e).1 he)
      obtain ⟨e₀, he₀S, he₀min⟩ := S.exists_min_image f hSne
      set lam : ℝ := f e₀ with hlam
      have hlampos : 0 < lam := hSpos e₀ he₀S
      set f' : Fin m → ℝ := fun e => f e - lam * traversalVector C e with hf'
      have hf'val : ∀ e, f' e = if e ∈ S then f e - lam else f e := by
        intro e
        by_cases he : e ∈ S
        · rw [hf', if_pos he]
          simp [htv, (hmemS e).1 he]
        · rw [hf', if_neg he]
          have : (e, true) ∉ C := fun h => he ((hmemS e).2 h)
          simp [htv, this]
      have hf'nn : 0 ≤ f' := by
        intro e
        simp only [Pi.zero_apply]
        rw [hf'val e]
        by_cases he : e ∈ S
        · rw [if_pos he]
          linarith [he₀min e he]
        · rw [if_neg he]
          simpa using hnn e
      have hf'circ : IsCirculation arcs f' := by
        have hC : IsCirculation arcs (traversalVector C) :=
          LinearOptimization.traversalVector_isCirculation_of_isCycle arcs hcyc
        funext i
        have h1 : (incidenceMatrix arcs).mulVec f' i
            = (incidenceMatrix arcs).mulVec f i - lam * (incidenceMatrix arcs).mulVec (traversalVector C) i := by
          simp only [Matrix.mulVec, dotProduct, hf', Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun e _ => by ring)
        rw [h1, congrFun hcirc i, congrFun hC i]
        simp
      -- the support strictly shrinks
      have hsub : supp f' ⊆ (supp f).erase e₀ := by
        intro e he
        have hne : f' e ≠ 0 := mem_supp.1 he
        refine Finset.mem_erase.2 ⟨?_, mem_supp.2 ?_⟩
        · intro hee
          apply hne
          rw [hf'val e, hee, if_pos he₀S, hlam]
          ring
        · intro hfe
          apply hne
          rw [hf'val e]
          have hnS : e ∉ S := fun hS' => by
            have := hSpos e hS'
            rw [hfe] at this; exact lt_irrefl _ this
          rw [if_neg hnS, hfe]
      have hcard' : (supp f').card ≤ N := by
        have h2 : e₀ ∈ supp f := mem_supp.2 (ne_of_gt (hSpos e₀ he₀S))
        have h1 : (supp f').card ≤ ((supp f).erase e₀).card := Finset.card_le_card hsub
        have h3 : ((supp f).erase e₀).card = (supp f).card - 1 := Finset.card_erase_of_mem h2
        have h4 : 0 < (supp f).card := Finset.card_pos.2 ⟨e₀, h2⟩
        omega
      obtain ⟨k, cyc, a, hcycles, hfwds, has, hsum, hint⟩ := ih f' hcard' hf'nn hf'circ
      refine ⟨k + 1, Fin.cons C cyc, Fin.cons lam a, ?_, ?_, ?_, ?_, ?_⟩
      · intro i
        refine Fin.cases ?_ ?_ i
        · exact ⟨v, hcyc⟩
        · intro j; simpa using hcycles j
      · intro i
        refine Fin.cases ?_ ?_ i
        · simpa using hfwd
        · intro j; simpa using hfwds j
      · intro i
        refine Fin.cases ?_ ?_ i
        · simpa using hlampos
        · intro j; simpa using has j
      · funext e
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ]
        have := congrFun hsum e
        simp only [hf'] at this
        rw [← this]
        ring
      · intro hfz i
        have hf'z : ∀ e, ∃ z : ℤ, f' e = (z : ℝ) := by
          intro e
          obtain ⟨w, hw⟩ := hfz e
          obtain ⟨w₀, hw₀⟩ := hfz e₀
          rw [hf'val e]
          by_cases he : e ∈ S
          · exact ⟨w - w₀, by simp only [he, if_true, hw, hlam, hw₀]; push_cast; ring⟩
          · exact ⟨w, by simp [he, hw]⟩
        refine Fin.cases ?_ ?_ i
        · obtain ⟨w₀, hw₀⟩ := hfz e₀
          exact ⟨w₀, by simpa [hlam] using hw₀⟩
        · intro j; simpa using hint hf'z j

end FlowDecomp

open LinearOptimization FlowDecomp
open Matrix

theorem solution {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (hloop : HasNoSelfLoops arcs)
    (f : Fin m → ℝ) (hnn : 0 ≤ f) (hcirc : IsCirculation arcs f)
    (hne : f ≠ 0) :
    (∃ (k : ℕ) (cyc : Fin k → List (Fin m × Bool)) (a : Fin k → ℝ),
      (∀ i, ∃ v, IsCycle arcs v (cyc i)) ∧
      (∀ i, ∀ st ∈ cyc i, st.2 = true) ∧
      (∀ i, 0 < a i) ∧
      f = fun e => ∑ i, a i * traversalVector (cyc i) e) ∧
    ((∀ e, ∃ z : ℤ, f e = (z : ℝ)) →
      ∃ (k : ℕ) (cyc : Fin k → List (Fin m × Bool)) (a : Fin k → ℤ),
        (∀ i, ∃ v, IsCycle arcs v (cyc i)) ∧
        (∀ i, ∀ st ∈ cyc i, st.2 = true) ∧
        (∀ i, 0 < a i) ∧
        f = fun e => ∑ i, (a i : ℝ) * traversalVector (cyc i) e) := by
  classical
  obtain ⟨k, cyc, a, hcycles, hfwds, has, hsum, hint⟩ :=
    decompose hloop (supp f).card f le_rfl hnn hcirc
  refine ⟨⟨k, cyc, a, hcycles, hfwds, has, hsum⟩, ?_⟩
  intro hfz
  refine ⟨k, cyc, fun i => (hint hfz i).choose, hcycles, hfwds, ?_, ?_⟩
  · intro i
    have h := (hint hfz i).choose_spec
    have := has i
    rw [h] at this
    exact_mod_cast this
  · rw [hsum]
    funext e
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [(hint hfz i).choose_spec]
