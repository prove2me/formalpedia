-- Prove2me | solution 1 for SoftmaxLookup.sum_weight_erase_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T04:38:30.47398+00:00
-- url     : https://prove2.me/submissions/c65cd925-0c49-46b0-aa21-223b75c52dd7

import Definitions.Def_MachineLearning_TransformerUniversality_SoftmaxLookup

/-
Faithful proof port from the Aether Catalog in Paul Klemstine's Lean repository:
https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/MachineLearning/TransformerUniversality/SoftmaxLookup.lean
The mathematical argument and tactic proofs below come from that source.
Only namespace organization and the top-level solution entry point are adapted.
This is source reuse, not a claim of a new mathematical discovery.
-/

open scoped BigOperators
open SoftmaxLookup

namespace SoftmaxPort

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem weight_le_exp_gap (beta : ℝ) (s : ι → ℝ) (i₀ j : ι) :
    weight beta s j ≤ Real.exp (beta * s j - beta * s i₀) := by
  have hden : Real.exp (beta * s i₀) ≤ ∑ k, Real.exp (beta * s k) :=
    Finset.single_le_sum (f := fun k => Real.exp (beta * s k))
      (fun k _ => le_of_lt (Real.exp_pos _)) (Finset.mem_univ i₀)
  have hpos : (0:ℝ) < Real.exp (beta * s i₀) := Real.exp_pos _
  rw [weight, Real.exp_sub]
  exact div_le_div_of_nonneg_left (le_of_lt (Real.exp_pos _)) hpos hden

end SoftmaxPort

open SoftmaxPort

theorem solution {ι : Type*} [Fintype ι] [DecidableEq ι] (beta gamma : ℝ) (s : ι → ℝ) (i₀ : ι)
    (hbeta : 0 ≤ beta) (hgap : ∀ j, j ≠ i₀ → s j + gamma ≤ s i₀) :
    ∑ j ∈ Finset.univ.erase i₀, weight beta s j
      ≤ (Fintype.card ι - 1 : ℝ) * Real.exp (-(beta * gamma)) := by
  have hterm : ∀ j ∈ Finset.univ.erase i₀,
      weight beta s j ≤ Real.exp (-(beta * gamma)) := by
    intro j hj
    have hne : j ≠ i₀ := Finset.ne_of_mem_erase hj
    refine (weight_le_exp_gap beta s i₀ j).trans ?_
    apply Real.exp_le_exp.mpr
    have h := hgap j hne
    nlinarith [h]
  refine (Finset.sum_le_card_nsmul _ _ _ hterm).trans ?_
  have hcard : (Finset.univ.erase i₀).card = Fintype.card ι - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i₀), Finset.card_univ]
  rw [nsmul_eq_mul, hcard]
  have h1 : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hcast : ((Fintype.card ι - 1 : ℕ) : ℝ) = (Fintype.card ι : ℝ) - 1 := by
    have := Nat.cast_sub (R := ℝ) h1
    simpa using this
  rw [hcast]
