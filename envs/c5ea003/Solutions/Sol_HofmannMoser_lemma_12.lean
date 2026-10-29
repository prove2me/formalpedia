-- Prove2me | solution 1 for HofmannMoser.lemma_12
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T22:34:20.590028+00:00
-- url     : https://prove2.me/submissions/1b4ae18a-a20b-4c9b-92a8-ea5da9dbe1bb

import Definitions.Def_HofmannMoser_Potential
import Mathlib

universe u

open HofmannMoser in
theorem solution {C : Nat → Type u} {m n : Nat} (P : RepPolicy C)
    (c : C n) (Q : Annotation C (m + 1))
    (ws : Fin m → Value C) (vs : Fin n → Value C) :
    potential Q (Fin.addCases ws (fun _ ↦ Value.node c vs)) =
      potential (additiveShift P c Q) (Fin.addCases ws vs) := by
  classical
  have hfold : ∀ (l : List ℕ) (a : ℕ), l.foldl (· * ·) a = a * l.prod := by
    intro l
    induction l with
    | nil => intro a; simp
    | cons x l ih => intro a; simp [List.foldl, ih, mul_assoc]
  have hmvb : ∀ {k : Nat} (ps : Fin k → BasicFunction C) (vals : Fin k → Value C),
      multivariateBasic ps vals = ∏ i, (ps i).val (vals i) := by
    intro k ps vals
    unfold multivariateBasic
    rw [hfold, one_mul, List.prod_ofFn]
  have hrc : ∀ (A : TreeAutomaton C) (q : Fin A.stateCount) (v : Value C)
      (s : Fin (A.reroot q).stateCount), (A.reroot q).runCount v s = A.runCount v s := by
    intro A q v
    induction v with
    | node c ch ih =>
      intro s
      rw [TreeAutomaton.runCount.eq_1 (A.reroot q), TreeAutomaton.runCount.eq_1 A s]
      congr 1
      apply List.map_congr_left
      intro tr _
      congr 1
      congr 1
      funext i
      exact ih i (tr.1 i)
  have hnode : ∀ p : BasicFunction C, p.val (Value.node c vs) =
      ((((P.rep p).rules n c).filter (fun tr ↦ tr.2 == (P.rep p).final)).map
        fun tr ↦ ∏ j, (BasicFunction.reroot (P.rep p) (tr.1 j)).val (vs j)).sum := by
    intro p
    rw [← P.rep_basic p]
    unfold TreeAutomaton.basic
    rw [TreeAutomaton.runCount.eq_1 (P.rep p) (P.rep p).final]
    congr 1
    apply List.map_congr_left
    intro tr _
    rw [hfold, one_mul, List.prod_ofFn]
    apply Finset.prod_congr rfl
    intro j _
    simp only [BasicFunction.reroot, BasicFunction.ofAutomaton, TreeAutomaton.basic]
    exact (hrc (P.rep p) (tr.1 j) (vs j) (tr.1 j)).symm
  have hl : Fin.natAdd m (0 : Fin 1) = Fin.last m := by ext; simp
  have hent : ∀ τ : Fin (m + 1) → BasicFunction C,
      ((multivariateBasic τ (Fin.addCases ws (fun _ ↦ Value.node c vs)) : ℕ) : ℚ) =
        ((shiftTuples P c τ).map fun t ↦ ((multivariateBasic t (Fin.addCases ws vs) : ℕ) : ℚ)).sum := by
    intro τ
    simp only [hmvb]
    rw [Fin.prod_univ_add, Fin.prod_univ_one]
    simp only [Fin.addCases_left, Fin.addCases_right]
    rw [hl, hnode]
    unfold shiftTuples
    simp only [List.map_map, Function.comp_def]
    simp only [Fin.prod_univ_add, Fin.addCases_left, Fin.addCases_right]
    push_cast
    rw [List.map_map, ← List.sum_map_mul_left]
    congr 1
    apply List.map_congr_left
    intro tr _
    simp only [Function.comp_apply]
    push_cast
    rfl
  unfold potential additiveShift
  induction Q with
  | nil => simp
  | cons e Q ih =>
    rw [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih,
      hent e.1, List.map_map, ← List.sum_map_mul_left]
    congr 1
