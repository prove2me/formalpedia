-- Prove2me | solution 1 for TemporalGLDeep.valid_iff_valid_on_bounded
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:44:58.067541+00:00
-- url     : https://prove2.me/submissions/46f2a8cf-7c08-4f22-9252-daaec1879f91

import Mathlib
import Definitions.Def_Logic_PosetTheory_TemporalGL
import Definitions.Def_Logic_PosetTheory_TemporalGLFiniteModel
import Definitions.Def_Logic_PosetTheory_TemporalGLSyntax

set_option maxHeartbeats 1000000 in
open TemporalGLDeep in
theorem solution (A : TForm) :
    Valid A ↔ ∀ (N : TempModel) (v : N.F.W), Finite N.F.W →
      Nat.card N.F.W ≤ 2 ^ (2 * subformulaCount A) → N.sat v A := by
  classical
  -- the filtration truth lemma (proved inline; same argument as `truth_lemma`)
  have htruth : ∀ (M : TempModel) (A : TForm),
      ∀ B, B ∈ subformulas A → ∀ u : M.F.W,
        (filtModel M A).sat (thetaW M A u) B ↔ M.sat u B := by
    intro M A
    classical
    intro B
    induction B with
    | atom p =>
        intro hB u
        constructor
        · intro h
          exact ((mem_theta M A).1 h).2
        · intro h
          exact (mem_theta M A).2 ⟨hB, h⟩
    | bot =>
        intro _ u
        exact Iff.rfl
    | imp C D ihC ihD =>
        intro hB u
        have hC : C ∈ subformulas A :=
          subformulas_subset hB (by simp [subformulas, self_mem_subformulas])
        have hD : D ∈ subformulas A :=
          subformulas_subset hB (by simp [subformulas, self_mem_subformulas])
        constructor
        · intro h hc
          exact (ihD hD u).1 (h ((ihC hC u).2 hc))
        · intro h hc
          exact (ihD hD u).2 (h ((ihC hC u).1 hc))
    | box C ih =>
        intro hB u
        have hC : C ∈ subformulas A :=
          subformulas_subset hB (by simp [subformulas, self_mem_subformulas])
        constructor
        · -- filtered truth of `◻C` gives real truth, via an `R`-maximal counterexample
          intro h
          by_contra hcon
          have hex : ∃ v, M.F.R u v ∧ ¬ M.sat v C := by
            by_contra hno
            push_neg at hno
            exact hcon (fun v hv => hno v hv)
          obtain ⟨m, ⟨hum, hmC⟩, hmin⟩ :=
            M.F.R_wf.has_min {v | M.F.R u v ∧ ¬ M.sat v C} (by
              obtain ⟨v, hv⟩ := hex; exact ⟨v, hv⟩)
          -- `m` is `R`-maximal among the counterexamples, so `◻C` holds at `m`
          have hboxm : M.sat m (TForm.box C) := by
            intro w hw
            by_contra hwC
            exact hmin w ⟨M.F.R_trans hum hw, hwC⟩ hw
          -- hence `theta m` is a filtered successor of `theta u`
          have hfilt : filtR (subformulas A) (thetaW M A u).1 (thetaW M A m).1 := by
            refine ⟨fun E hE hEu => ?_, ⟨C, hB, ?_, ?_⟩⟩
            · have hEu' := (mem_theta M A).1 hEu
              have hEsub : E ∈ subformulas A :=
                subformulas_subset hE (by simp [subformulas, self_mem_subformulas])
              refine ⟨(mem_theta M A).2 ⟨hEsub, hEu'.2 m hum⟩,
                (mem_theta M A).2 ⟨hE, ?_⟩⟩
              intro w hw
              exact hEu'.2 w (M.F.R_trans hum hw)
            · exact (mem_theta M A).2 ⟨hB, hboxm⟩
            · intro hc
              exact hcon ((mem_theta M A).1 hc).2
          exact hmC ((ih hC m).1 (h (thetaW M A m) hfilt))
        · -- real truth of `◻C` gives filtered truth
          intro h S hS
          obtain ⟨v, rfl⟩ := exists_rep M A S
          have hCv : M.sat v C := by
            have hbox : (TForm.box C) ∈ (thetaW M A u).1 :=
              (mem_theta M A).2 ⟨hB, h⟩
            exact ((mem_theta M A).1 (hS.1 C hB hbox).1).2
          exact (ih hC v).2 hCv
    | glob C ih =>
        intro hB u
        have hC : C ∈ subformulas A := mem_subformulas_glob hB
        constructor
        · -- `compat` is exactly what makes this direction work without a maximality argument
          intro h
          intro v hv
          have hfilt : filtT (subformulas A) (thetaW M A u).1 (thetaW M A v).1 := by
            refine ⟨fun E hE hEu => ?_, fun E hE hEu => ?_⟩
            · have hEu' := (mem_theta M A).1 hEu
              have hEsub : E ∈ subformulas A := mem_subformulas_glob hE
              refine ⟨(mem_theta M A).2 ⟨hEsub, hEu'.2 v hv⟩,
                (mem_theta M A).2 ⟨hE, ?_⟩⟩
              intro w hw
              exact hEu'.2 w (M.F.T_trans hv hw)
            · have hEu' := (mem_theta M A).1 hEu
              refine (mem_theta M A).2 ⟨hE, ?_⟩
              intro w hw
              exact hEu'.2 w (M.F.compat hv hw)
          exact (ih hC v).1 (h (thetaW M A v) hfilt)
        · intro h S hS
          obtain ⟨v, rfl⟩ := exists_rep M A S
          have hCv : M.sat v C := by
            have hglob : (TForm.glob C) ∈ (thetaW M A u).1 :=
              (mem_theta M A).2 ⟨hB, h⟩
            exact ((mem_theta M A).1 (hS.1 C hB hglob).1).2
          exact (ih hC v).2 hCv
  -- the filtered model is small
  have hcard : ∀ (M : TempModel) (A : TForm),
      Nat.card (FWorld M A) ≤ 2 ^ subformulaCount A := by
    intro M A
    have h1 : Nat.card (FWorld M A) = (Wset M A).card := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_coe _
    have h2 : (Wset M A).card ≤ ((subformulas A).powerset).card :=
      Finset.card_filter_le _ _
    rw [h1, Finset.card_powerset] at *
    exact h2
  constructor
  · intro h N v _ _
    exact h N v
  · intro h M w
    by_contra hcon
    have hfin : Finite (filtModel M A).F.W := by
      change Finite (FWorld M A)
      infer_instance
    have hle : Nat.card (filtModel M A).F.W ≤ 2 ^ (2 * subformulaCount A) := by
      have hEq : Nat.card (filtModel M A).F.W = Nat.card (FWorld M A) := rfl
      rw [hEq]
      exact le_trans (hcard M A) (Nat.pow_le_pow_right (by norm_num) (by omega))
    have := h (filtModel M A) (thetaW M A w) hfin hle
    exact hcon ((htruth M A A (self_mem_subformulas A) w).1 this)
