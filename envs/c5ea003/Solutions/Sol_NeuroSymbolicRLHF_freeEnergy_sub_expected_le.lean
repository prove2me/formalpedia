-- Prove2me | solution 1 for NeuroSymbolicRLHF.freeEnergy_sub_expected_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:12:35.256016+00:00
-- url     : https://prove2.me/submissions/5a6136bd-c8c3-4ec9-9674-129bf66bd2c3

-- Sol generated from Speculative/AutoResearch/RLHFFreeEnergyDuality.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
import Theorems.Thm_NeuroSymbolicRLHF_tiltZ_pos
/-
# Free-energy duality, annealing limits, and the exact PTX regression law

Second file of the neurosymbolic RLHF thread.  It builds on the catalog
definitions of `Speculative/AutoResearch/NeuroSymbolicRLHFObjective.lean`
(`tiltZ`, `gibbs`, `freeEnergy`, `rlhfObj`, `ptxTerm`) and on the oscillation
seminorm `oscil` introduced in `MachineLearning/RLHFHilbertIsometry.lean`.

Three independent layers, all about the *value function*
`F(β, r) = β log Z = max_p [𝔼_p r - β KL(p ‖ ref)]` of the InstructGPT
objective:

* **Level A — Legendre / Danskin duality (`hasDerivAt_freeEnergy`).**
  The directional derivative of the free energy with respect to the reward is
  the expectation of the direction under the *optimal* (tilted) policy:
  `d/dt|₀ F(β, r + t s) = 𝔼_{π_β(r)}[s]`.
  So the aligned policy is literally the gradient of the alignment value —
  an envelope theorem for RLHF.

* **Level B — annealing (thermodynamic limits).**
  Zero temperature: `max r + β log (min ref) ≤ F(β,r) ≤ max r`, hence
  `F(β,r) → max r` as `β → 0⁺` (reward maximisation, policy collapse).
  Infinite temperature: `0 ≤ F(β,r) - 𝔼_ref[r] ≤ (3/4)‖r‖_∞²/β` for
  `β ≥ ‖r‖_∞`, hence `F(β,r) → 𝔼_ref[r]` as `β → ∞` (the SFT model).
  Both limits come with explicit rates.

* **Level C — the exact PTX regression law (`ptx_at_gibbs`).**
  Evaluating the pre-training mix-in at the aligned policy gives the *identity*
  `𝔼_pre[log π_β(r)] = 𝔼_pre[log ref] + (𝔼_pre[r] - F(β,r))/β`.
  Hence RLHF regresses on the pre-training distribution exactly when the
  pre-training data scores below the free-energy level, and the regression is
  never worse than `γ · oscil r / β` — the same `1/β` scale that governs the
  Hilbert-metric drift of the policy itself.

No `sorry`, no `native_decide`.
-/

open Finset Real BigOperators Filter Topology

noncomputable section

open NeuroSymbolicRLHF

variable {ι : Type*} [Fintype ι] [Nonempty ι]

/-! ## Level A: the free energy is the potential of the aligned policy -/



/-! ## Level B: annealing limits with explicit rates -/




/-- Quadratic control of the exponential on `[-1,1]`, from Mathlib's Taylor
bound: `exp u ≤ 1 + u + (3/4) u²`. -/
theorem exp_le_quadratic {u : ℝ} (hu : |u| ≤ 1) :
    Real.exp u ≤ 1 + u + (3 / 4) * u ^ 2 := by
  have h := Real.exp_bound hu (n := 2) (by norm_num)
  have hsum : ∑ m ∈ Finset.range 2, u ^ m / (Nat.factorial m : ℝ) = 1 + u := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hsum] at h
  have h2 : Real.exp u - (1 + u) ≤ |u| ^ 2 * ((2 : ℕ).succ / ((Nat.factorial 2 : ℝ) * 2)) :=
    le_trans (le_abs_self _) h
  have habs : |u| ^ 2 = u ^ 2 := sq_abs u
  rw [habs] at h2
  norm_num [Nat.factorial] at h2
  linarith



/-! ## Level C: the exact PTX regression law -/





open NeuroSymbolicRLHF in
theorem solution{β M : ℝ} {ref r : ι → ℝ} (href : IsPosProb ref)
    (hM : ∀ i, |r i| ≤ M) (hMpos : 0 < M) (hβ : M ≤ β) :
    freeEnergy β ref r - (∑ i, ref i * r i) ≤ (3 / 4) * M ^ 2 / β := by
  have hβpos : 0 < β := lt_of_lt_of_le hMpos hβ
  have hu : ∀ i, |r i / β| ≤ 1 := by
    intro i
    rw [abs_div, abs_of_pos hβpos, div_le_one hβpos]
    exact le_trans (hM i) hβ
  have hZle : tiltZ β ref r ≤ 1 + (∑ i, ref i * r i) / β + (3 / 4) * M ^ 2 / β ^ 2 := by
    have hstep : ∀ i ∈ (univ : Finset ι),
        ref i * Real.exp (r i / β)
          ≤ ref i * (1 + r i / β + (3 / 4) * (M ^ 2 / β ^ 2)) := by
      intro i _
      refine mul_le_mul_of_nonneg_left ?_ (href.pos i).le
      refine le_trans (exp_le_quadratic (hu i)) ?_
      have hsq : (r i / β) ^ 2 ≤ M ^ 2 / β ^ 2 := by
        rw [div_pow, div_le_div_iff_of_pos_right (by positivity)]
        have := abs_le.mp (hM i)
        nlinarith [abs_nonneg (r i), sq_abs (r i), abs_le.mp (hM i)]
      linarith
    calc tiltZ β ref r ≤ ∑ i, ref i * (1 + r i / β + (3 / 4) * (M ^ 2 / β ^ 2)) :=
          Finset.sum_le_sum hstep
      _ = 1 + (∑ i, ref i * r i) / β + (3 / 4) * M ^ 2 / β ^ 2 := by
          have hA : ∑ i, ref i * (1 + r i / β + (3 / 4) * (M ^ 2 / β ^ 2))
              = ∑ i, (ref i + ref i * r i / β + ref i * ((3 / 4) * (M ^ 2 / β ^ 2))) :=
            Finset.sum_congr rfl fun i _ => by ring
          have h2 : ∑ i, ref i * r i / β = (∑ i, ref i * r i) / β := by
            rw [Finset.sum_div]
          have h3 : ∑ i, ref i * ((3 / 4) * (M ^ 2 / β ^ 2)) = (3 / 4) * M ^ 2 / β ^ 2 := by
            rw [← Finset.sum_mul, href.sum_one, one_mul]; ring
          rw [hA, Finset.sum_add_distrib, Finset.sum_add_distrib, href.sum_one, h2, h3]
  have hZpos : 0 < tiltZ β ref r := tiltZ_pos href
  have hlog : Real.log (tiltZ β ref r) ≤ tiltZ β ref r - 1 :=
    Real.log_le_sub_one_of_pos hZpos
  have hkey : Real.log (tiltZ β ref r) ≤ (∑ i, ref i * r i) / β + (3 / 4) * M ^ 2 / β ^ 2 := by
    linarith
  have := mul_le_mul_of_nonneg_left hkey hβpos.le
  simp only [freeEnergy]
  have hexp : β * ((∑ i, ref i * r i) / β + (3 / 4) * M ^ 2 / β ^ 2)
      = (∑ i, ref i * r i) + (3 / 4) * M ^ 2 / β := by
    field_simp
  linarith [hexp ▸ this]
