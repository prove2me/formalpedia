-- Prove2me | solution 1 for NeuroSymbolicRLHF.freeEnergy_ge_max_add
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T16:45:02.030503+00:00
-- url     : https://prove2.me/submissions/15fe027f-64ff-4ec0-95e3-4b8ceda42486

import Mathlib
import Definitions.Def_Speculative_AutoResearch_NeuroSymbolicRLHFObjective
import Definitions.Def_Speculative_AutoResearch_RLHFHilbertIsometry
open NeuroSymbolicRLHF Finset in
theorem solution {ι : Type*} [Fintype ι] [Nonempty ι] {β : ℝ} (hβ : 0 < β) {ref r : ι → ℝ}
    (href : IsPosProb ref) :
    (univ.sup' univ_nonempty r) + β * Real.log (univ.inf' univ_nonempty ref)
      ≤ freeEnergy β ref r := by
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
  -- and `ref i₀ ≥ min ref > 0`
  obtain ⟨j₀, -, hj₀⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty ref
  have hinf : univ.inf' univ_nonempty ref ≤ ref i₀ := Finset.inf'_le ref (Finset.mem_univ i₀)
  have hinfpos : 0 < univ.inf' univ_nonempty ref := by rw [hj₀]; exact hpos j₀
  have hlog := Real.log_le_log hinfpos hinf
  have := hlow0 β hβ
  nlinarith [mul_le_mul_of_nonneg_left hlog hβ.le]
