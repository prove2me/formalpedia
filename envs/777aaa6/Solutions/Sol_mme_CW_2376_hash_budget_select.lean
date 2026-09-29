-- Prove2me | solution 1 for mme_CW_2376_hash_budget_select
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T22:33:07.600381+00:00
-- url     : https://prove2.me/submissions/1d4ce53a-cff1-4c55-bd14-887d7c4e2225

import Theorems.Thm_mme_CW_2376_hash_incidence_sums
import Theorems.Thm_mme_CW_2376_augmented_hash_state_universe_card
import Theorems.Thm_mme_CW_2376_marginal_hash_retained_vertex_closed
import Theorems.Thm_mme_finite_collision_budget_averaging_real

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

/-- An aggregate real collision budget selects one augmented hash state whose
full retained ambient hypergraph is vertex-closed and has the desired target
surplus. -/
theorem solution
    (m p : ℕ) (hm : 0 < m) [Fact p.Prime]
    (hp5 : 5 ≤ p) (hpodd : Odd p)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ)) (L : ℝ)
    (hbudget :
      (p : ℝ) ^ (cw2376ProfileLength m + 2) * L +
          ((cw2376AllTargetAmbientCollisions m).card : ℝ) *
            (p : ℝ) ^ cw2376ProfileLength m ≤
        ((cw2376AllExactTargetEdges m).card : ℝ) *
          (S.card : ℝ) * (p : ℝ) ^ cw2376ProfileLength m) :
    ∃ q : (Fin (cw2376ProfileLength m + 1) → ZMod p) × ZMod p,
      let E := cw2376RetainedEdgesAtAugmentedState m p S q
      CW2376MarginalVertexClosed E ∧
        ((cw2376TargetAmbientCollisions E).card : ℝ) + L ≤
          ((cw2376ExactTargetEdges E).card : ℝ) := by
  classical
  let good :
      ((Fin (cw2376ProfileLength m + 1) → ZMod p) × ZMod p) → ℕ :=
    fun q => (cw2376ExactTargetEdges
      (cw2376RetainedEdgesAtAugmentedState m p S q)).card
  let bad :
      ((Fin (cw2376ProfileLength m + 1) → ZMod p) × ZMod p) → ℕ :=
    fun q => (cw2376TargetAmbientCollisions
      (cw2376RetainedEdgesAtAugmentedState m p S q)).card
  have hinc := mme_CW_2376_hash_incidence_sums
    m p hm hp5 hpodd S hSrange
  have hgoodNat :
      (∑ q, good q) =
        (cw2376AllExactTargetEdges m).card * S.card *
          p ^ cw2376ProfileLength m := by
    simpa only [good, cw2376AugmentedHashStateUniverse,
      Finset.sum_const_zero] using hinc.1
  have hbadNat :
      (∑ q, bad q) ≤
        (cw2376AllTargetAmbientCollisions m).card *
          p ^ cw2376ProfileLength m := by
    simpa only [bad, cw2376AugmentedHashStateUniverse,
      Finset.sum_const_zero] using hinc.2
  have hgoodReal :
      (∑ q, (good q : ℝ)) =
        ((cw2376AllExactTargetEdges m).card : ℝ) *
          (S.card : ℝ) * (p : ℝ) ^ cw2376ProfileLength m := by
    exact_mod_cast hgoodNat
  have hbadReal :
      (∑ q, (bad q : ℝ)) ≤
        ((cw2376AllTargetAmbientCollisions m).card : ℝ) *
          (p : ℝ) ^ cw2376ProfileLength m := by
    exact_mod_cast hbadNat
  have hcard :
      Fintype.card
          ((Fin (cw2376ProfileLength m + 1) → ZMod p) × ZMod p) =
        p ^ (cw2376ProfileLength m + 2) := by
    simpa only [cw2376AugmentedHashStateUniverse, Finset.card_univ] using
      mme_CW_2376_augmented_hash_state_universe_card m p
  have havgBudget :
      (Fintype.card
          ((Fin (cw2376ProfileLength m + 1) → ZMod p) × ZMod p) : ℝ) * L +
          ∑ q, (bad q : ℝ) ≤
        ∑ q, (good q : ℝ) := by
    calc
      (Fintype.card
          ((Fin (cw2376ProfileLength m + 1) → ZMod p) × ZMod p) : ℝ) * L +
          ∑ q, (bad q : ℝ) ≤
          (p : ℝ) ^ (cw2376ProfileLength m + 2) * L +
            ((cw2376AllTargetAmbientCollisions m).card : ℝ) *
              (p : ℝ) ^ cw2376ProfileLength m := by
        rw [hcard]
        push_cast
        simpa only [add_comm] using
          add_le_add_left hbadReal
            ((p : ℝ) ^ (cw2376ProfileLength m + 2) * L)
      _ ≤ ((cw2376AllExactTargetEdges m).card : ℝ) *
            (S.card : ℝ) * (p : ℝ) ^ cw2376ProfileLength m := hbudget
      _ = ∑ q, (good q : ℝ) := hgoodReal.symm
  obtain ⟨q, hq⟩ :=
    mme_finite_collision_budget_averaging_real good bad L havgBudget
  refine ⟨q, ?_, ?_⟩
  · exact mme_CW_2376_marginal_hash_retained_vertex_closed
      m p S q.2 (fun j => q.1 j.castSucc) hpodd hSrange hSfree
  · exact hq
