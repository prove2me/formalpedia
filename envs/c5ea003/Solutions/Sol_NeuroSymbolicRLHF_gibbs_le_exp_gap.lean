-- Prove2me | solution 1 for NeuroSymbolicRLHF.gibbs_le_exp_gap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:22:47.275683+00:00
-- url     : https://prove2.me/submissions/c3c39de3-7923-4a37-abf4-92049da95dd7

-- Sol generated from Speculative/AutoResearch/NeuroSymbolicRLHFPareto.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Theorems.Thm_NeuroSymbolicRLHF_tiltZ_pos
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
theorem solution{β : ℝ} (hβ : 0 < β) {ref r : ι → ℝ} [Nonempty ι]
    (href : IsPosProb ref) (i0 i : ι) :
    gibbs β ref r i ≤ (ref i / ref i0) * Real.exp (-((r i0 - r i) / β)) := by
  have hZ : 0 < tiltZ β ref r := tiltZ_pos href
  have hterm : ref i0 * Real.exp (r i0 / β) ≤ tiltZ β ref r := by
    unfold tiltZ
    refine Finset.single_le_sum (f := fun j => ref j * Real.exp (r j / β)) ?_ (Finset.mem_univ i0)
    intro j _
    exact (mul_pos (href.pos j) (Real.exp_pos _)).le
  have hnum : ref i * Real.exp (r i / β)
      ≤ (ref i / ref i0) * Real.exp (-((r i0 - r i) / β)) * (ref i0 * Real.exp (r i0 / β)) := by
    have hsplit : (ref i / ref i0) * Real.exp (-((r i0 - r i) / β)) * (ref i0 * Real.exp (r i0 / β))
        = ref i * (Real.exp (-((r i0 - r i) / β)) * Real.exp (r i0 / β)) := by
      have h0 : ref i0 ≠ 0 := (href.pos i0).ne'
      field_simp
    have hexp : Real.exp (-((r i0 - r i) / β)) * Real.exp (r i0 / β) = Real.exp (r i / β) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    rw [hsplit, hexp]
  have hc : 0 ≤ (ref i / ref i0) * Real.exp (-((r i0 - r i) / β)) := by
    have := href.pos i; have := href.pos i0
    positivity
  have : ref i * Real.exp (r i / β)
      ≤ (ref i / ref i0) * Real.exp (-((r i0 - r i) / β)) * tiltZ β ref r :=
    le_trans hnum (mul_le_mul_of_nonneg_left hterm hc)
  unfold gibbs
  rw [div_le_iff₀ hZ]
  exact this
