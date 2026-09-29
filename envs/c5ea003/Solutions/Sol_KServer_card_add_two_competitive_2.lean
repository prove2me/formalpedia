-- Prove2me | solution 2 for KServer.card_add_two_competitive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T11:11:02.424606+00:00
-- url     : https://prove2.me/submissions/223781ee-fa91-4ad3-b920-8aa5bc205ad3

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_extended_cost_lemma_injective
import Theorems.Thm_KServer_workFnU_growth_card_add_two_inj

open KServer

/-- Spaces of exactly `k + 2` points: the Work Function Algorithm is `k`-competitive.
This is the Extended Cost Lemma applied with `lam = k + 1`. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    [Fintype M] (hM : Fintype.card M = k + 2) (C₀ : Config k M) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A (k : ℝ) := by
  classical
  -- on a space of `k + 2` points an injective configuration exists
  have h1 : 1 < Fintype.card M := by rw [hM]; omega
  obtain ⟨p, q, hpq⟩ := Fintype.exists_pair_of_one_lt_card h1
  have hc : Fintype.card {x : M // x ≠ p ∧ x ≠ q} = k := by
    rw [Fintype.card_subtype]
    have hset : (Finset.univ.filter (fun x : M => x ≠ p ∧ x ≠ q))
        = (Finset.univ.erase p).erase q := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true, true_and]
      tauto
    rw [hset,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hpq, Finset.mem_univ q⟩),
      Finset.card_erase_of_mem (Finset.mem_univ p), Finset.card_univ, hM]
    omega
  set X₀ : Config k M := fun i => ((Fintype.equivFinOfCardEq hc).symm i : M) with hX₀def
  have hX₀ : Function.Injective X₀ := by
    intro a b hab
    exact (Fintype.equivFinOfCardEq hc).symm.injective (Subtype.ext hab)
  obtain ⟨c, hgrowth⟩ := workFnU_growth_card_add_two_inj k hk M hM C₀
  obtain ⟨A, hA0, hA⟩ :=
    extended_cost_lemma_injective k hk M C₀ X₀ hX₀ ((k : ℝ) + 1) c hgrowth
  refine ⟨A, hA0, ?_⟩
  have e : (k : ℝ) + 1 - 1 = (k : ℝ) := by ring
  rwa [e] at hA
