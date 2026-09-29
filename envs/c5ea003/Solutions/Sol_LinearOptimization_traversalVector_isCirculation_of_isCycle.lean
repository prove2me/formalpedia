-- Prove2me | solution 1 for LinearOptimization.traversalVector_isCirculation_of_isCycle
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T15:57:59.288954+00:00
-- url     : https://prove2.me/submissions/85072bc4-a39c-4090-9c41-516f8a2a198e

import Definitions.Def_LinearOptimization_NetworkFlowProblem
import Mathlib.Tactic.Ring

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

theorem solution {n m : ℕ} (arcs : Fin m → Fin n × Fin n) {v : Fin n}
    {steps : List (Fin m × Bool)}
    (hcyc : LinearOptimization.IsCycle arcs v steps) :
    LinearOptimization.IsCirculation arcs
      (LinearOptimization.traversalVector steps) := by
  rcases hcyc with ⟨_, hwalk, _, hedges⟩
  rw [LinearOptimization.IsCirculation]
  simpa using
    (LinearOptimization.incidence_mulVec_traversalVector_of_walk
      arcs hwalk hedges)
