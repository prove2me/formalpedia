-- Prove2me | solution 1 for RademacherWigner.markov
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:40:50.590982+00:00
-- url     : https://prove2.me/submissions/41dcf8ca-acda-429b-afde-0165c8fb2b7d

/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license.

Proof port from Paul Klemstine's Aether Catalog, commit 53c2925a02:
Catalog/Probability/WignerSpectralEdge.lean, lines 41–53.
Expectation is fully qualified to distinguish it from Finset.expect.
-/
import Definitions.Def_Probability_WignerSpectralEdge
import Theorems.Thm_RademacherWigner_card_config_pos

set_option autoImplicit false

open Matrix BigOperators Finset RademacherWigner

variable {N : ℕ}

theorem solution(f : Config N → ℝ) (hf : ∀ g, 0 ≤ f g) {c : ℝ} (hc : 0 < c) :
    RademacherWigner.prob (Finset.univ.filter fun g : Config N => c ≤ f g)
      ≤ RademacherWigner.expect f / c := by
  classical
  set A : Finset (Config N) := Finset.univ.filter fun g : Config N => c ≤ f g with hA
  have h1 : c * (A.card : ℝ) ≤ ∑ g ∈ A, f g := by
    calc c * (A.card : ℝ) = ∑ _g ∈ A, c := by
          rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ g ∈ A, f g := Finset.sum_le_sum fun g hg => (Finset.mem_filter.1 hg).2
  have h2 : ∑ g ∈ A, f g ≤ ∑ g : Config N, f g :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun g _ _ => hf g
  have hM : (0 : ℝ) < (Fintype.card (Config N) : ℝ) := card_config_pos N
  rw [RademacherWigner.prob, RademacherWigner.expect, div_div,
    div_le_div_iff₀ hM (by positivity)]
  nlinarith [h1, h2, hM.le, hc.le, Nat.cast_nonneg (α := ℝ) A.card]
