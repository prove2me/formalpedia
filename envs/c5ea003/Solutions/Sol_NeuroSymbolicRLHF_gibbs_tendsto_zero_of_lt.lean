-- Prove2me | solution 1 for NeuroSymbolicRLHF.gibbs_tendsto_zero_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:24:07.028461+00:00
-- url     : https://prove2.me/submissions/5e85d8ab-9796-490f-acec-90ce649cf46e

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFPareto.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Theorems.Thm_NeuroSymbolicRLHF_gibbs_le_exp_gap
import Theorems.Thm_NeuroSymbolicRLHF_gibbs_pos
/-
Copyright (c) 2025. All rights reserved.

# The Alignment Pareto Frontier and the Low-Temperature Limit of RLHF

Fourth research cycle, building on
`Catalog.Shared.NeuroSymbolicRLHFObjective`.

* **Pareto monotonicity of the KL coefficient.**  Lowering `β` moves the RLHF
  optimum monotonically along a frontier: both the KL divergence from the SFT
  policy *and* the achieved expected reward increase.  The proof is a pure
  exchange argument between the two optimality inequalities — no differentiation
  of the free energy in `β` is needed, so no smoothness hypotheses appear.

* **Low-temperature limit.**  As `β → 0⁺` the optimal value converges to the
  maximal reward, and every strictly suboptimal response is asymptotically
  abandoned by the aligned policy.  Together with `gibbs_tendsto_ref`
  (`β → ∞`, aligned policy → SFT policy) this pins down both ends of the
  frontier.

No `sorry`, no `native_decide`.
-/

open Finset Real BigOperators Filter Topology

noncomputable section

open NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι]

/-! ## The Pareto frontier in the KL coefficient -/




/-! ## The low-temperature limit `β → 0⁺` -/






open NeuroSymbolicRLHF in
theorem solution{ref r : ι → ℝ} [Nonempty ι] (href : IsPosProb ref)
    {i0 i : ι} (hlt : r i < r i0) :
    Tendsto (fun β : ℝ => gibbs β ref r i) (𝓝[>] 0) (𝓝 0) := by
  set δ := r i0 - r i with hδ
  have hδpos : 0 < δ := by simp [hδ]; linarith
  have hquot : Tendsto (fun β : ℝ => δ / β) (𝓝[>] 0) atTop := by
    have h := tendsto_inv_nhdsGT_zero.const_mul_atTop hδpos
    simpa [div_eq_mul_inv] using h
  have hexp : Tendsto (fun β : ℝ => Real.exp (-(δ / β))) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun β : ℝ => Real.exp (δ / β)) (𝓝[>] 0) atTop :=
      Real.tendsto_exp_atTop.comp hquot
    have h2 := h1.inv_tendsto_atTop
    simpa [Real.exp_neg] using h2
  have hbound : Tendsto (fun β : ℝ => (ref i / ref i0) * Real.exp (-(δ / β))) (𝓝[>] 0) (𝓝 0) := by
    have := hexp.const_mul (ref i / ref i0)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    exact (gibbs_pos href i).le
  · filter_upwards [self_mem_nhdsWithin] with β hβ
    exact gibbs_le_exp_gap hβ href i0 i
