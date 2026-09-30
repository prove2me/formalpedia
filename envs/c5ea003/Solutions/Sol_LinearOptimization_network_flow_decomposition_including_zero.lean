-- Prove2me | solution 1 for LinearOptimization.network_flow_decomposition_including_zero
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:05:12.835959+00:00
-- url     : https://prove2.me/submissions/ae1bd498-43a6-477a-acf9-64def267fda3

import Mathlib
import Definitions.Def_LinearOptimization_NetworkFlowProblem

set_option autoImplicit false

-- Accepted source by Harry_Xu; submission 62a4e5ad-b8e0-49b4-9665-f272b0b00971.
-- Imports removed and solution renamed to the original helper theorem name; proof body unchanged.
open Matrix

namespace LinearOptimization

private lemma circulation_balance {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (f : Fin m → ℝ)
    (hcirc : IsCirculation arcs f) (v : Fin n) :
    (∑ e, if (arcs e).1 = v then f e else 0) =
      ∑ e, if (arcs e).2 = v then f e else 0 := by
  have hv := congrFun hcirc v
  simp only [IsCirculation, Matrix.mulVec, dotProduct, incidenceMatrix,
    Matrix.of_apply, Pi.zero_apply] at hv
  simp_rw [sub_mul] at hv
  rw [Finset.sum_sub_distrib] at hv
  simp_rw [ite_mul, one_mul, zero_mul] at hv
  linarith

private lemma positive_outgoing_from_positive_incoming {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (f : Fin m → ℝ)
    (hnn : 0 ≤ f) (hcirc : IsCirculation arcs f)
    (e : Fin m) (he : 0 < f e) :
    ∃ e' : Fin m, (arcs e').1 = (arcs e).2 ∧ 0 < f e' := by
  let v := (arcs e).2
  have hin_nonneg : ∀ e' : Fin m,
      0 ≤ if (arcs e').2 = v then f e' else 0 := by
    intro e'
    split
    · exact hnn e'
    · exact le_rfl
  have hin_pos : 0 < ∑ e', if (arcs e').2 = v then f e' else 0 := by
    apply Finset.sum_pos'
    · intro e' _
      exact hin_nonneg e'
    · refine ⟨e, Finset.mem_univ _, ?_⟩
      simpa [v] using he
  have hout_pos : 0 < ∑ e', if (arcs e').1 = v then f e' else 0 := by
    rw [circulation_balance arcs f hcirc v]
    exact hin_pos
  by_contra hnone
  push_neg at hnone
  have hzero : ∀ e' : Fin m,
      (if (arcs e').1 = v then f e' else 0) = 0 := by
    intro e'
    by_cases htail : (arcs e').1 = v
    · simp only [htail, ↓reduceIte]
      exact le_antisymm (hnone e' htail) (hnn e')
    · simp [htail]
  simp_rw [hzero] at hout_pos
  simp at hout_pos

private lemma isWalkFrom_ofFn_forward {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (edge : ℕ → Fin m)
    (hlink : ∀ r, (arcs (edge r)).2 = (arcs (edge (r + 1))).1)
    (p d : ℕ) :
    IsWalkFrom arcs (arcs (edge p)).1 (arcs (edge (p + d))).1
      (List.ofFn fun a : Fin d => (edge (p + a), true)) := by
  induction d generalizing p with
  | zero => simp [IsWalkFrom]
  | succ d ih =>
      rw [List.ofFn_succ]
      simp only [IsWalkFrom]
      constructor
      · simp [stepStart]
      · simp only [stepEnd, if_pos rfl, Fin.val_zero, Nat.add_zero]
        rw [hlink p]
        simpa [Fin.succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          (ih (p + 1))

end LinearOptimization

theorem LinearOptimization.positive_directed_cycle_of_circulation {n m : ℕ} (arcs : Fin m → Fin n × Fin n)
    (hloop : LinearOptimization.HasNoSelfLoops arcs) (f : Fin m → ℝ)
    (hnn : 0 ≤ f) (hcirc : LinearOptimization.IsCirculation arcs f)
    (hne : f ≠ 0) :
    ∃ (v : Fin n) (steps : List (Fin m × Bool)),
      LinearOptimization.IsCycle arcs v steps ∧
      (∀ st ∈ steps, st.2 = true) ∧
      ∀ st ∈ steps, 0 < f st.1 := by
  classical
  have hex_pos : ∃ e : Fin m, 0 < f e := by
    by_contra h
    push_neg at h
    apply hne
    funext e
    exact le_antisymm (h e) (hnn e)
  let PosEdge := {e : Fin m // 0 < f e}
  let e₀ : PosEdge := ⟨Classical.choose hex_pos, Classical.choose_spec hex_pos⟩
  let next : PosEdge → PosEdge := fun e =>
    ⟨Classical.choose
        (LinearOptimization.positive_outgoing_from_positive_incoming
          arcs f hnn hcirc e.1 e.2),
      (Classical.choose_spec
        (LinearOptimization.positive_outgoing_from_positive_incoming
          arcs f hnn hcirc e.1 e.2)).2⟩
  have hnext (e : PosEdge) :
      (arcs (next e).1).1 = (arcs e.1).2 :=
    (Classical.choose_spec
      (LinearOptimization.positive_outgoing_from_positive_incoming
        arcs f hnn hcirc e.1 e.2)).1
  let es : ℕ → PosEdge := fun r => (next^[r]) e₀
  have hes_succ (r : ℕ) : es (r + 1) = next (es r) := by
    simp [es, Function.iterate_succ_apply']
  have hlink (r : ℕ) :
      (arcs (es r).1).2 = (arcs (es (r + 1)).1).1 := by
    rw [hes_succ]
    exact (hnext (es r)).symm
  let vs : ℕ → Fin n := fun r => (arcs (es r).1).1
  obtain ⟨i, j, hij, hvij⟩ :=
    Finite.exists_ne_map_eq_of_infinite vs
  have hperiod_exists :
      ∃ d : ℕ, 0 < d ∧ ∃ p : ℕ, vs p = vs (p + d) := by
    rcases lt_or_gt_of_ne hij with hijlt | hjilt
    · refine ⟨j - i, by omega, i, ?_⟩
      simpa [Nat.add_sub_of_le hijlt.le] using hvij
    · refine ⟨i - j, by omega, j, ?_⟩
      simpa [Nat.add_sub_of_le hjilt.le] using hvij.symm
  let d := Nat.find hperiod_exists
  have hd_spec : 0 < d ∧ ∃ p : ℕ, vs p = vs (p + d) :=
    Nat.find_spec hperiod_exists
  have hd_pos : 0 < d := hd_spec.1
  obtain ⟨p, hperiod⟩ := hd_spec.2
  have hvs_inj : Function.Injective (fun a : Fin d => vs (p + a)) := by
    intro a b hab
    apply Fin.ext
    by_contra habne
    rcases lt_or_gt_of_ne habne with halt | hblt
    · have hsmall : b.val - a.val < d := by omega
      have hshort : 0 < b.val - a.val ∧
          ∃ q : ℕ, vs q = vs (q + (b.val - a.val)) := by
        refine ⟨by omega, p + a.val, ?_⟩
        have hidx : p + a.val + (b.val - a.val) = p + b.val := by omega
        simpa [hidx] using hab
      exact (Nat.find_min hperiod_exists hsmall) hshort
    · have hsmall : a.val - b.val < d := by omega
      have hshort : 0 < a.val - b.val ∧
          ∃ q : ℕ, vs q = vs (q + (a.val - b.val)) := by
        refine ⟨by omega, p + b.val, ?_⟩
        have hidx : p + b.val + (a.val - b.val) = p + a.val := by omega
        simpa [hidx] using hab.symm
      exact (Nat.find_min hperiod_exists hsmall) hshort
  let steps : List (Fin m × Bool) :=
    List.ofFn fun a : Fin d => ((es (p + a)).1, true)
  refine ⟨vs p, steps, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro hnil
      have : steps.length = 0 := by simp [hnil]
      simp [steps, hd_pos.ne'] at this
    · have hw := LinearOptimization.isWalkFrom_ofFn_forward
        arcs (fun r => (es r).1) hlink p d
      change LinearOptimization.IsWalkFrom arcs (vs p) (vs p) steps
      change LinearOptimization.IsWalkFrom arcs (vs p) (vs (p + d)) steps at hw
      simpa only [hperiod] using hw
    · have hnodes :
          LinearOptimization.walkNodes arcs (vs p) steps =
            List.ofFn (fun a : Fin (d + 1) => vs (p + a)) := by
        simp only [LinearOptimization.walkNodes, steps, vs, List.map_ofFn,
          Function.comp_apply, LinearOptimization.stepEnd, if_pos rfl]
        rw [List.ofFn_succ]
        congr 1
        apply List.ofFn_inj.mpr
        funext a
        simp only [Function.comp_apply, LinearOptimization.stepEnd, if_pos rfl]
        rw [hlink]
        congr 3
      rw [hnodes, List.ofFn_succ']
      simp only [List.concat_eq_append, List.dropLast_concat]
      simpa using (List.nodup_ofFn.mpr hvs_inj)
    · simp only [steps, List.map_ofFn]
      apply List.nodup_ofFn.mpr
      intro a b hab
      apply hvs_inj
      change vs (p + a) = vs (p + b)
      simp only [vs]
      change (es (p + a)).1 = (es (p + b)).1 at hab
      rw [hab]
  · intro st hst
    simp only [steps, List.mem_ofFn] at hst
    rcases hst with ⟨a, rfl⟩
    rfl
  · intro st hst
    simp only [steps, List.mem_ofFn] at hst
    rcases hst with ⟨a, rfl⟩
    exact (es (p + a)).2

-- Accepted source by Harry_Xu; submission 81747003-52d3-48aa-a638-9c6b23b76d01.
-- Imports removed and solution renamed to the original helper theorem name; proof body unchanged.
open Matrix

namespace LinearOptimization

private def signedStepVector {m : ℕ} (st : Fin m × Bool) : Fin m → ℝ :=
  fun e => if e = st.1 then if st.2 then 1 else -1 else 0

private lemma traversalVector_cons_of_fst_not_mem {m : ℕ}
    (st : Fin m × Bool) (rest : List (Fin m × Bool))
    (hnot : st.1 ∉ rest.map Prod.fst) :
    traversalVector (st :: rest) =
      fun e => signedStepVector st e + traversalVector rest e := by
  rcases st with ⟨e₀, dir⟩
  have hntrue : (e₀, true) ∉ rest := by
    intro hmem
    apply hnot
    exact List.mem_map.mpr ⟨(e₀, true), hmem, rfl⟩
  have hnfalse : (e₀, false) ∉ rest := by
    intro hmem
    apply hnot
    exact List.mem_map.mpr ⟨(e₀, false), hmem, rfl⟩
  funext e
  by_cases he : e = e₀
  · subst e
    cases dir <;> simp [traversalVector, signedStepVector, hntrue, hnfalse]
  · cases dir <;> simp [traversalVector, signedStepVector, he]

private lemma incidence_mulVec_signedStepVector {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (st : Fin m × Bool) :
    (incidenceMatrix arcs).mulVec (signedStepVector st) =
      fun i => (if stepStart arcs st = i then 1 else 0) -
        (if stepEnd arcs st = i then 1 else 0) := by
  funext i
  rw [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single st.1]
  · rcases st with ⟨e, dir⟩
    cases dir <;>
      simp [incidenceMatrix, signedStepVector, stepStart, stepEnd]
  · intro b _ hb
    simp [signedStepVector, hb]
  · simp

private lemma incidence_mulVec_traversalVector_of_walk {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) {s t : Fin n}
    {steps : List (Fin m × Bool)}
    (hwalk : IsWalkFrom arcs s t steps)
    (hnodup : (steps.map Prod.fst).Nodup) :
    (incidenceMatrix arcs).mulVec (traversalVector steps) =
      fun i => (if s = i then 1 else 0) - (if t = i then 1 else 0) := by
  induction steps generalizing s with
  | nil =>
      simp only [IsWalkFrom] at hwalk
      subst t
      funext i
      simp [traversalVector, Matrix.mulVec, dotProduct]
  | cons st rest ih =>
      simp only [IsWalkFrom] at hwalk
      rcases hwalk with ⟨hstart, hrest⟩
      have hnot : st.1 ∉ rest.map Prod.fst := by
        simpa using (List.nodup_cons.mp hnodup).1
      have hrestnodup : (rest.map Prod.fst).Nodup := by
        simpa using (List.nodup_cons.mp hnodup).2
      rw [traversalVector_cons_of_fst_not_mem st rest hnot]
      change (incidenceMatrix arcs).mulVec
        (signedStepVector st + traversalVector rest) = _
      rw [Matrix.mulVec_add]
      rw [incidence_mulVec_signedStepVector arcs st]
      rw [ih hrest hrestnodup]
      funext i
      rw [← hstart]
      simp only [Pi.add_apply]
      ring

end LinearOptimization

theorem LinearOptimization.traversalVector_isCirculation_of_isCycle {n m : ℕ} (arcs : Fin m → Fin n × Fin n) {v : Fin n}
    {steps : List (Fin m × Bool)}
    (hcyc : LinearOptimization.IsCycle arcs v steps) :
    LinearOptimization.IsCirculation arcs
      (LinearOptimization.traversalVector steps) := by
  rcases hcyc with ⟨_, hwalk, _, hedges⟩
  rw [LinearOptimization.IsCirculation]
  funext i
  simpa using congrFun (LinearOptimization.incidence_mulVec_traversalVector_of_walk
      arcs hwalk hedges) i

-- Accepted source by Grace; submission 058017ae-2b90-4451-b061-624e940a8445.
-- Imports removed. The unused nonzero binder was removed from solution; its proof body is unchanged, and its existing support induction handles the empty-flow case.
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
    :
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
