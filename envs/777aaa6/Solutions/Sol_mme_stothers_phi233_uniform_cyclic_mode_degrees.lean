-- Prove2me | solution 1 for mme_stothers_phi233_uniform_cyclic_mode_degrees
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-03T00:08:59.878818+00:00
-- url     : https://prove2.me/submissions/2a72c4ea-a264-4641-a277-2f2287659ade

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Theorems.Thm_mme_stothers_phi233_marginal_star_factorization
import Theorems.Thm_mme_stothers_phi233_exact_star_factorization
import Theorems.Thm_mme_stothers_phi233_cyclic_finset_cardinalities

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000
set_option warningAsError true

private def tripleFiberEquiv'
    {A X Y Z : Type} (f : A → X) (g : A → Y) (h : A → Z)
    (a b c : A) :
    {e : A × (A × A) //
        (f e.1, (g e.2.1, h e.2.2)) = (f a, (g b, h c))} ≃
      {x : A // f x = f a} ×
        ({y : A // g y = g b} × {z : A // h z = h c}) where
  toFun e :=
    (⟨e.1.1, congrArg (fun w ↦ w.1) e.2⟩,
      (⟨e.1.2.1, congrArg (fun w ↦ w.2.1) e.2⟩,
        ⟨e.1.2.2, congrArg (fun w ↦ w.2.2) e.2⟩))
  invFun x := ⟨(x.1.1, (x.2.1.1, x.2.2.1)), by
    apply Prod.ext
    · exact x.1.2
    · apply Prod.ext
      · exact x.2.1.2
      · exact x.2.2.2⟩
  left_inv e := by apply Subtype.ext; rfl
  right_inv x := by rfl

/-- The concrete cyclic target and ambient finsets have uniform mode degree.
The common target-cardinality factor is the product of the three mode-word
multinomial counts. -/
theorem solution
    (N alpha beta gamma delta : ℕ)
    (hsum : 2 * alpha + beta + gamma + delta = N)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta)
    [DecidableEq (MME.StothersFourth.Phi233.CyclicModeWord N)] :
    let D := ∏ l : Fin 3,
      Nat.card
        {b : MME.StothersFourth.Phi233.MarginalAddress
            N alpha beta gamma delta // b.1 l = a.1.1 l}
    let Dstar := ∏ l : Fin 3,
      Nat.card
        {b : MME.StothersFourth.Phi233.ExactProfileAddress
            N alpha beta gamma delta // b.1.1 l = a.1.1 l}
    let V := ∏ l : Fin 3,
      ((2 * N).factorial /
        ∏ s : Fin 5,
          (MME.StothersFourth.Phi233.marginalMultiplicity
            alpha beta gamma delta l s).factorial)
    (∀ i : Fin 3,
      ∀ e ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ((MME.StothersFourth.Phi233.ambientFinset
            N alpha beta gamma delta).filter
          (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
            MME.StothersFourth.Phi233.cyclicModeWord e i)).card = D) ∧
    (∀ i : Fin 3,
      ∀ e ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ((MME.StothersFourth.Phi233.targetFinset
            N alpha beta gamma delta).filter
          (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
            MME.StothersFourth.Phi233.cyclicModeWord e i)).card = Dstar) ∧
    (MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta).card = V * Dstar := by
  classical
  let Profile := MME.StothersFourth.Phi233.ProfileAddress N
  let Marginal := MME.StothersFourth.Phi233.MarginalAddress
    N alpha beta gamma delta
  let Exact := MME.StothersFourth.Phi233.ExactProfileAddress
    N alpha beta gamma delta
  let AmbEdge := MME.StothersFourth.Phi233.CyclicAmbientEdge
    N alpha beta gamma delta
  let ExactEdge := MME.StothersFourth.Phi233.CyclicExactEdge
    N alpha beta gamma delta
  letI : Fintype Profile :=
    inferInstanceAs (Fintype (Fin 3 → Fin (2 * N) → Fin 5))
  letI : Fintype Marginal :=
    @Subtype.fintype _ _ (Classical.decPred _) inferInstance
  letI : Fintype Exact :=
    @Subtype.fintype _ _ (Classical.decPred _) inferInstance
  letI : Fintype AmbEdge := by
    dsimp only [AmbEdge, MME.StothersFourth.Phi233.CyclicAmbientEdge]
    infer_instance
  letI : Fintype ExactEdge := by
    dsimp only [ExactEdge, MME.StothersFourth.Phi233.CyclicExactEdge]
    infer_instance
  let AStar : Exact → Fin 3 → ℕ := fun x l ↦ Nat.card
    {b : Marginal // b.1 l = x.1.1 l}
  let TStar : Exact → Fin 3 → ℕ := fun x l ↦ Nat.card
    {b : Exact // b.1.1 l = x.1.1 l}
  let W : Fin 3 → ℕ := fun l ↦
    (2 * N).factorial /
      ∏ s : Fin 5,
        (MME.StothersFourth.Phi233.marginalMultiplicity
          alpha beta gamma delta l s).factorial
  let D : ℕ := ∏ l : Fin 3, AStar a l
  let Dstar : ℕ := ∏ l : Fin 3, TStar a l
  let V : ℕ := ∏ l : Fin 3, W l
  have hexactPos : 0 < Nat.card Exact := by
    letI : Nonempty Exact := ⟨a⟩
    exact Nat.card_pos
  have hwordPos (l : Fin 3) : 0 < W l := by
    have h := mme_stothers_phi233_exact_star_factorization
      N alpha beta gamma delta hsum a l
    change Nat.card Exact = W l * TStar a l at h
    rw [h] at hexactPos
    exact Nat.pos_of_mul_pos_right hexactPos
  have hAStarEq (x : Exact) (l : Fin 3) : AStar x l = AStar a l := by
    have hx := mme_stothers_phi233_marginal_star_factorization
      N alpha beta gamma delta x.1 l
    have ha := mme_stothers_phi233_marginal_star_factorization
      N alpha beta gamma delta a.1 l
    change Nat.card Marginal = W l * AStar x l at hx
    change Nat.card Marginal = W l * AStar a l at ha
    exact Nat.mul_left_cancel (hwordPos l) (hx.symm.trans ha)
  have hTStarEq (x : Exact) (l : Fin 3) : TStar x l = TStar a l := by
    have hx := mme_stothers_phi233_exact_star_factorization
      N alpha beta gamma delta hsum x l
    have ha := mme_stothers_phi233_exact_star_factorization
      N alpha beta gamma delta hsum a l
    change Nat.card Exact = W l * TStar x l at hx
    change Nat.card Exact = W l * TStar a l at ha
    exact Nat.mul_left_cancel (hwordPos l) (hx.symm.trans ha)
  have hDexpand : D =
      AStar a 0 * (AStar a 1 * AStar a 2) := by
    simp [D, Fin.prod_univ_succ]
  have hDstarExpand : Dstar =
      TStar a 0 * (TStar a 1 * TStar a 2) := by
    simp [Dstar, Fin.prod_univ_succ]
  have hambSubtype (t : ExactEdge) (i : Fin 3) :
      Nat.card {e : AmbEdge //
        MME.StothersFourth.Phi233.cyclicModeWord e i =
          MME.StothersFourth.Phi233.cyclicModeWord
            (MME.StothersFourth.Phi233.exactToAmbient t) i} = D := by
    fin_cases i
    · let e := tripleFiberEquiv'
        (fun b : Marginal ↦ b.1 (0 : Fin 3))
        (fun b : Marginal ↦ b.1 (2 : Fin 3))
        (fun b : Marginal ↦ b.1 (1 : Fin 3)) t.1.1 t.2.1.1 t.2.2.1
      calc
        Nat.card {x : AmbEdge //
            MME.StothersFourth.Phi233.cyclicModeWord x 0 =
              MME.StothersFourth.Phi233.cyclicModeWord
                (MME.StothersFourth.Phi233.exactToAmbient t) 0} =
            AStar t.1 0 * (AStar t.2.1 2 * AStar t.2.2 1) := by
          rw [← Nat.card_prod, ← Nat.card_prod]
          exact Nat.card_congr e
        _ = D := by
          rw [hAStarEq t.1 0, hAStarEq t.2.1 2, hAStarEq t.2.2 1]
          rw [hDexpand]
          ac_rfl
    · let e := tripleFiberEquiv'
        (fun b : Marginal ↦ b.1 (1 : Fin 3))
        (fun b : Marginal ↦ b.1 (0 : Fin 3))
        (fun b : Marginal ↦ b.1 (2 : Fin 3)) t.1.1 t.2.1.1 t.2.2.1
      calc
        Nat.card {x : AmbEdge //
            MME.StothersFourth.Phi233.cyclicModeWord x 1 =
              MME.StothersFourth.Phi233.cyclicModeWord
                (MME.StothersFourth.Phi233.exactToAmbient t) 1} =
            AStar t.1 1 * (AStar t.2.1 0 * AStar t.2.2 2) := by
          rw [← Nat.card_prod, ← Nat.card_prod]
          exact Nat.card_congr e
        _ = D := by
          rw [hAStarEq t.1 1, hAStarEq t.2.1 0, hAStarEq t.2.2 2]
          rw [hDexpand]
          ac_rfl
    · let e := tripleFiberEquiv'
        (fun b : Marginal ↦ b.1 (2 : Fin 3))
        (fun b : Marginal ↦ b.1 (1 : Fin 3))
        (fun b : Marginal ↦ b.1 (0 : Fin 3)) t.1.1 t.2.1.1 t.2.2.1
      calc
        Nat.card {x : AmbEdge //
            MME.StothersFourth.Phi233.cyclicModeWord x 2 =
              MME.StothersFourth.Phi233.cyclicModeWord
                (MME.StothersFourth.Phi233.exactToAmbient t) 2} =
            AStar t.1 2 * (AStar t.2.1 1 * AStar t.2.2 0) := by
          rw [← Nat.card_prod, ← Nat.card_prod]
          exact Nat.card_congr e
        _ = D := by
          rw [hAStarEq t.1 2, hAStarEq t.2.1 1, hAStarEq t.2.2 0]
          rw [hDexpand]
          ac_rfl
  have htargetSubtype (t : ExactEdge) (i : Fin 3) :
      Nat.card {e : ExactEdge //
        MME.StothersFourth.Phi233.cyclicModeWord
            (MME.StothersFourth.Phi233.exactToAmbient e) i =
          MME.StothersFourth.Phi233.cyclicModeWord
            (MME.StothersFourth.Phi233.exactToAmbient t) i} = Dstar := by
    fin_cases i
    · let e := tripleFiberEquiv'
        (fun b : Exact ↦ b.1.1 (0 : Fin 3))
        (fun b : Exact ↦ b.1.1 (2 : Fin 3))
        (fun b : Exact ↦ b.1.1 (1 : Fin 3)) t.1 t.2.1 t.2.2
      calc
        Nat.card {x : ExactEdge //
            MME.StothersFourth.Phi233.cyclicModeWord
                (MME.StothersFourth.Phi233.exactToAmbient x) 0 =
              MME.StothersFourth.Phi233.cyclicModeWord
                (MME.StothersFourth.Phi233.exactToAmbient t) 0} =
            TStar t.1 0 * (TStar t.2.1 2 * TStar t.2.2 1) := by
          rw [← Nat.card_prod, ← Nat.card_prod]
          exact Nat.card_congr e
        _ = Dstar := by
          rw [hTStarEq t.1 0, hTStarEq t.2.1 2, hTStarEq t.2.2 1]
          rw [hDstarExpand]
          ac_rfl
    · let e := tripleFiberEquiv'
        (fun b : Exact ↦ b.1.1 (1 : Fin 3))
        (fun b : Exact ↦ b.1.1 (0 : Fin 3))
        (fun b : Exact ↦ b.1.1 (2 : Fin 3)) t.1 t.2.1 t.2.2
      calc
        Nat.card {x : ExactEdge //
            MME.StothersFourth.Phi233.cyclicModeWord
                (MME.StothersFourth.Phi233.exactToAmbient x) 1 =
              MME.StothersFourth.Phi233.cyclicModeWord
                (MME.StothersFourth.Phi233.exactToAmbient t) 1} =
            TStar t.1 1 * (TStar t.2.1 0 * TStar t.2.2 2) := by
          rw [← Nat.card_prod, ← Nat.card_prod]
          exact Nat.card_congr e
        _ = Dstar := by
          rw [hTStarEq t.1 1, hTStarEq t.2.1 0, hTStarEq t.2.2 2]
          rw [hDstarExpand]
          ac_rfl
    · let e := tripleFiberEquiv'
        (fun b : Exact ↦ b.1.1 (2 : Fin 3))
        (fun b : Exact ↦ b.1.1 (1 : Fin 3))
        (fun b : Exact ↦ b.1.1 (0 : Fin 3)) t.1 t.2.1 t.2.2
      calc
        Nat.card {x : ExactEdge //
            MME.StothersFourth.Phi233.cyclicModeWord
                (MME.StothersFourth.Phi233.exactToAmbient x) 2 =
              MME.StothersFourth.Phi233.cyclicModeWord
                (MME.StothersFourth.Phi233.exactToAmbient t) 2} =
            TStar t.1 2 * (TStar t.2.1 1 * TStar t.2.2 0) := by
          rw [← Nat.card_prod, ← Nat.card_prod]
          exact Nat.card_congr e
        _ = Dstar := by
          rw [hTStarEq t.1 2, hTStarEq t.2.1 1, hTStarEq t.2.2 0]
          rw [hDstarExpand]
          ac_rfl
  have hambFilter (t : ExactEdge) (i : Fin 3) :
      ((MME.StothersFourth.Phi233.ambientFinset
          N alpha beta gamma delta).filter
        (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
          MME.StothersFourth.Phi233.cyclicModeWord
            (MME.StothersFourth.Phi233.exactToAmbient t) i)).card = D := by
    rw [show MME.StothersFourth.Phi233.ambientFinset
      N alpha beta gamma delta = (Finset.univ : Finset AmbEdge) by
        ext e
        simp [MME.StothersFourth.Phi233.ambientFinset]]
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact hambSubtype t i
  have htargetFilter (t : ExactEdge) (i : Fin 3) :
      ((MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta).filter
        (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
          MME.StothersFourth.Phi233.cyclicModeWord
            (MME.StothersFourth.Phi233.exactToAmbient t) i)).card = Dstar := by
    rw [show MME.StothersFourth.Phi233.targetFinset
      N alpha beta gamma delta =
        (Finset.univ : Finset ExactEdge).map
          (MME.StothersFourth.Phi233.exactEmbedding
            N alpha beta gamma delta) by
        ext e
        simp [MME.StothersFourth.Phi233.targetFinset]]
    rw [Finset.filter_map, Finset.card_map]
    rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
    exact htargetSubtype t i
  have hambUniform : ∀ i : Fin 3,
      ∀ e ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ((MME.StothersFourth.Phi233.ambientFinset
            N alpha beta gamma delta).filter
          (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
            MME.StothersFourth.Phi233.cyclicModeWord e i)).card = D := by
    intro i e he
    rw [show MME.StothersFourth.Phi233.targetFinset
      N alpha beta gamma delta =
        (Finset.univ : Finset ExactEdge).map
          (MME.StothersFourth.Phi233.exactEmbedding
            N alpha beta gamma delta) by
        ext x
        simp [MME.StothersFourth.Phi233.targetFinset]] at he
    rcases Finset.mem_map.mp he with ⟨t, ht, hte⟩
    rw [← hte]
    exact hambFilter t i
  have htargetUniform : ∀ i : Fin 3,
      ∀ e ∈ MME.StothersFourth.Phi233.targetFinset
          N alpha beta gamma delta,
        ((MME.StothersFourth.Phi233.targetFinset
            N alpha beta gamma delta).filter
          (fun b ↦ MME.StothersFourth.Phi233.cyclicModeWord b i =
            MME.StothersFourth.Phi233.cyclicModeWord e i)).card = Dstar := by
    intro i e he
    rw [show MME.StothersFourth.Phi233.targetFinset
      N alpha beta gamma delta =
        (Finset.univ : Finset ExactEdge).map
          (MME.StothersFourth.Phi233.exactEmbedding
            N alpha beta gamma delta) by
        ext x
        simp [MME.StothersFourth.Phi233.targetFinset]] at he
    rcases Finset.mem_map.mp he with ⟨t, ht, hte⟩
    rw [← hte]
    exact htargetFilter t i
  have hfactor (l : Fin 3) : Nat.card Exact = W l * TStar a l := by
    simpa only [Exact, W, TStar] using
      (mme_stothers_phi233_exact_star_factorization
        N alpha beta gamma delta hsum a l)
  have hproduct : (Nat.card Exact) ^ 3 = V * Dstar := by
    calc
      (Nat.card Exact) ^ 3 = ∏ l : Fin 3, Nat.card Exact := by
        simp [pow_succ]
      _ = ∏ l : Fin 3, (W l * TStar a l) := by
        apply Finset.prod_congr rfl
        intro l hl
        exact hfactor l
      _ = V * Dstar := by
        rw [Finset.prod_mul_distrib]
  have htargetCard :
      (MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta).card = V * Dstar := by
    rw [(mme_stothers_phi233_cyclic_finset_cardinalities
      N alpha beta gamma delta).2.1]
    simpa only [Exact] using hproduct
  simpa only [D, Dstar, V, AStar, TStar, W] using
    And.intro hambUniform (And.intro htargetUniform htargetCard)
