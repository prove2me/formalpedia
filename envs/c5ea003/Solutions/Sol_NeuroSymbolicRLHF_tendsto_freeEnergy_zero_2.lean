-- Prove2me | solution 2 for NeuroSymbolicRLHF.tendsto_freeEnergy_zero
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T16:39:53.665245+00:00
-- url     : https://prove2.me/submissions/90e3350a-c0ca-44a6-8c1b-9e5f9e8b3e76

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
open NeuroSymbolicRLHF Finset Filter Topology in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {ref r : ι → ℝ} (href : IsPosProb ref) :
    Tendsto (fun β : ℝ => freeEnergy β ref r) (𝓝[>] (0 : ℝ))
      (𝓝 (univ.sup' univ_nonempty r)) := by
  have hpos := href.pos
  have hZ : ∀ β, 0 < tiltZ β ref r := fun β =>
    Finset.sum_pos (fun i _ => mul_pos (hpos i) (Real.exp_pos _)) Finset.univ_nonempty
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty r
  -- keep only a maximizing term: `F(β) ≥ max r + β log ref(i₀)`
  have hlow0 : ∀ β : ℝ, 0 < β →
      (univ.sup' univ_nonempty r) + β * Real.log (ref i₀) ≤ freeEnergy β ref r := by
    intro β hβ
    unfold freeEnergy
    have h1 : ref i₀ * Real.exp (r i₀ / β) ≤ tiltZ β ref r :=
      Finset.single_le_sum (f := fun i => ref i * Real.exp (r i / β))
        (fun i _ => (mul_pos (hpos i) (Real.exp_pos _)).le) (Finset.mem_univ i₀)
    have h2 := Real.log_le_log (mul_pos (hpos i₀) (Real.exp_pos _)) h1
    rw [Real.log_mul (hpos i₀).ne' (Real.exp_pos _).ne', Real.log_exp] at h2
    have h3 := mul_le_mul_of_nonneg_left h2 hβ.le
    have e : β * (Real.log (ref i₀) + r i₀ / β) = r i₀ + β * Real.log (ref i₀) := by
      field_simp
      ring
    rw [hi₀]
    linarith
  -- upper bound: `F(β) ≤ max r`
  have hle : ∀ i, r i ≤ univ.sup' univ_nonempty r := fun i => Finset.le_sup' r (Finset.mem_univ i)
  have hup : ∀ β : ℝ, 0 < β → freeEnergy β ref r ≤ univ.sup' univ_nonempty r := by
    intro β hβ
    unfold freeEnergy
    have hZle : tiltZ β ref r ≤ Real.exp (univ.sup' univ_nonempty r / β) := by
      calc tiltZ β ref r ≤ ∑ i, ref i * Real.exp (univ.sup' univ_nonempty r / β) := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            refine mul_le_mul_of_nonneg_left ?_ (hpos i).le
            exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (hle i) hβ.le)
        _ = Real.exp (univ.sup' univ_nonempty r / β) := by rw [← Finset.sum_mul, href.sum_one, one_mul]
    have hlog : Real.log (tiltZ β ref r) ≤ univ.sup' univ_nonempty r / β := by
      rw [Real.log_le_iff_le_exp (hZ β)]
      exact hZle
    calc β * Real.log (tiltZ β ref r) ≤ β * (univ.sup' univ_nonempty r / β) :=
          mul_le_mul_of_nonneg_left hlog hβ.le
      _ = univ.sup' univ_nonempty r := by field_simp
  -- squeeze as `β → 0⁺`
  have h0 : Tendsto (fun β : ℝ => β) (𝓝[>] 0) (𝓝 0) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hlim : Tendsto (fun β : ℝ => univ.sup' univ_nonempty r + β * Real.log (ref i₀)) (𝓝[>] 0)
      (𝓝 (univ.sup' univ_nonempty r)) := by
    have := tendsto_const_nhds (x := univ.sup' univ_nonempty r).add (h0.mul_const (Real.log (ref i₀)))
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds
    (eventually_nhdsWithin_of_forall (fun β hβ => hlow0 β hβ))
    (eventually_nhdsWithin_of_forall (fun β hβ => hup β hβ))
