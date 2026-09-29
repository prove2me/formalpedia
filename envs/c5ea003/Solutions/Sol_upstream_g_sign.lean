-- Prove2me | solution 1 for upstream_g_sign
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-21T20:28:42.422935+00:00
-- url     : https://prove2.me/submissions/0e3db04d-379c-4c6d-9387-8a729c0ffc5b

import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
open Set

-- Proved node cb4f43dc: boundary-aware StrictMonoOn on Icc from interior deriv (continuity on Icc).
theorem strictMonoOn_Icc_interior (f f' : ℝ → ℝ) (a b : ℝ)
    (hcont : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hpos : ∀ x ∈ Ioo a b, 0 < f' x) :
    StrictMonoOn f (Icc a b) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc a b) hcont
  intro x hx; rw [interior_Icc] at hx; rw [(hd x hx).deriv]; exact hpos x hx

-- analogous Anti version (to be proved as a sibling node, mirrors cb4f43dc with strictAntiOn_of_deriv_neg)
theorem strictAntiOn_Icc_interior (f f' : ℝ → ℝ) (a b : ℝ)
    (hcont : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x)
    (hneg : ∀ x ∈ Ioo a b, f' x < 0) :
    StrictAntiOn f (Icc a b) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc a b) hcont
  intro x hx; rw [interior_Icc] at hx; rw [(hd x hx).deriv]; exact hneg x hx

/-- **Upstream → g-sign-data (interior-crossing model).**
For the density `f > 0` on `(0,2µ)`, with `φ(x) = log f(x) - log f(2µ-x)` having a single
interior maximum at `a ∈ (0,µ)` (`φ' > 0` on `(0,a)`, `φ' < 0` on `(a,µ)`), `φ` continuous on
`(0,µ]`, and a point `t₀ ∈ (0,a)` with `φ(t₀) < 0` (true since `φ → -∞` at `0⁺`), and boundary
`g(0) = f(0) - f(2µ) ≤ 0`, the difference `g(x) = f(x) - f(2µ-x)` satisfies
`g ≤ 0 on [0,c]` and `g ≥ 0 on [c,µ]` for some crossing `c ∈ [0,µ]`. -/
theorem solution
    (f φ' : ℝ → ℝ) (μ a t₀ : ℝ) (hμ : 0 < μ) (ha : a ∈ Ioo (0:ℝ) μ)
    (hfpos : ∀ x ∈ Ioo (0:ℝ) (2*μ), 0 < f x)
    (hφd : ∀ x ∈ Ioo (0:ℝ) μ,
        HasDerivAt (fun y => Real.log (f y) - Real.log (f (2*μ - y))) (φ' x) x)
    (hφpos : ∀ x ∈ Ioo (0:ℝ) a, 0 < φ' x)
    (hφneg : ∀ x ∈ Ioo a μ, φ' x < 0)
    (hφcont : ContinuousOn (fun y => Real.log (f y) - Real.log (f (2*μ - y))) (Ioc 0 μ))
    (ht₀ : t₀ ∈ Ioo (0:ℝ) a) (hφt₀ : Real.log (f t₀) - Real.log (f (2*μ - t₀)) < 0)
    (hg0 : f 0 - f (2*μ) ≤ 0) :
    ∃ c ∈ Icc (0:ℝ) μ,
      (∀ x ∈ Icc (0:ℝ) c, f x - f (2*μ - x) ≤ 0)
        ∧ (∀ x ∈ Icc c μ, 0 ≤ f x - f (2*μ - x)) := by
  set φ : ℝ → ℝ := fun y => Real.log (f y) - Real.log (f (2*μ - y)) with hφ_def
  obtain ⟨ha0, haμ⟩ := ha
  -- φ(μ) = 0  (since 2µ-µ = µ)
  have hφμ : φ μ = 0 := by simp only [hφ_def]; rw [show 2*μ - μ = μ by ring]; ring
  -- φ > 0 on (a,μ): φ strictly anti on [a,μ], φ(μ)=0 ⟹ φ(x) > φ(μ) = 0
  have hcont_aμ : ContinuousOn φ (Icc a μ) := by
    apply hφcont.mono; intro x hx; rw [mem_Icc] at hx; rw [mem_Ioc]; exact ⟨by linarith, hx.2⟩
  have hanti : StrictAntiOn φ (Icc a μ) :=
    strictAntiOn_Icc_interior φ φ' a μ hcont_aμ
      (fun x hx => hφd x ⟨by have := hx.1; linarith [ha0], hx.2⟩) hφneg
  have hφpos_aμ : ∀ x ∈ Ioo a μ, 0 < φ x := by
    intro x hx
    obtain ⟨hax, hxμ⟩ := hx
    have := hanti ⟨hax.le, hxμ.le⟩ ⟨haμ.le, le_refl μ⟩ hxμ
    rw [hφμ] at this; linarith
  -- φ strictly mono on [t₀, a]
  have hcont_t₀a : ContinuousOn φ (Icc t₀ a) := by
    apply hφcont.mono; intro x hx; rw [mem_Icc] at hx; rw [mem_Ioc]
    exact ⟨by linarith [ht₀.1], by linarith [haμ]⟩
  have hmono : StrictMonoOn φ (Icc t₀ a) :=
    strictMonoOn_Icc_interior φ φ' t₀ a hcont_t₀a
      (fun x hx => hφd x ⟨by linarith [ht₀.1, hx.1], by linarith [haμ, hx.2]⟩)
      (fun x hx => hφpos x ⟨by linarith [ht₀.1, hx.1], hx.2⟩)
  -- φ(a) > 0  (limit point: take x ∈ (a,μ), φ(a) ... use continuity at a from the right via hanti? )
  -- Simpler: φ(a) ≥ 0. From hmono φ(t₀) < φ(a). And φ(t₀)<0. Need φ(a)≥0:
  -- φ is continuous on [a,μ], strictly anti, so φ(a) > φ(x) for x∈(a,μ], φ(μ)=0 ⟹ φ(a) > 0.
  have hφa : 0 < φ a := by
    rcases eq_or_lt_of_le haμ.le with h | h
    · exact absurd h (ne_of_lt haμ)
    · have hmid : (a + μ)/2 ∈ Ioo a μ := ⟨by linarith, by linarith⟩
      have := hanti ⟨le_refl a, haμ.le⟩ ⟨by linarith [hmid.1], by linarith [hmid.2]⟩ hmid.1
      have hpos := hφpos_aμ _ hmid
      linarith
  -- crossing c ∈ (t₀, a): φ(t₀) < 0 < φ(a), IVT on [t₀,a]
  obtain ⟨c, hc_mem, hc_zero⟩ : ∃ c ∈ Ioo t₀ a, φ c = 0 := by
    have hsign : (0:ℝ) ∈ Ioo (φ t₀) (φ a) := ⟨hφt₀, hφa⟩
    obtain ⟨c, hc, hv⟩ := intermediate_value_Ioo ht₀.2.le hcont_t₀a hsign
    exact ⟨c, hc, hv⟩
  obtain ⟨ht₀c, hca⟩ := hc_mem
  have hc0 : 0 < c := lt_trans ht₀.1 ht₀c
  have hcμ : c < μ := lt_trans hca haμ
  refine ⟨c, ⟨hc0.le, hcμ.le⟩, ?_, ?_⟩
  · -- g ≤ 0 on [0,c]
    intro x hx
    rw [mem_Icc] at hx
    obtain ⟨hx0, hxc⟩ := hx
    rcases eq_or_lt_of_le hx0 with hxeq | hx0'
    · -- x = 0
      rw [← hxeq]; simpa using hg0
    · -- x ∈ (0,c]: φ(x) ≤ 0 ⟹ g(x) ≤ 0
      have hxμ : x < μ := lt_of_le_of_lt hxc hcμ
      have hfx : 0 < f x := hfpos x ⟨hx0', by linarith⟩
      have hf2 : 0 < f (2*μ - x) := hfpos (2*μ - x) ⟨by linarith, by linarith⟩
      have hφx_le : φ x ≤ 0 := by
        rcases lt_or_ge x t₀ with hxt | hxt
        · -- x < t₀: φ(x) < φ(t₀) < 0  (φ mono on [x,t₀])
          have hcont_xt : ContinuousOn φ (Icc x t₀) := by
            apply hφcont.mono; intro y hy; rw [mem_Icc] at hy; rw [mem_Ioc]
            exact ⟨by linarith, by linarith [ht₀.2, haμ]⟩
          have hmono_xt : StrictMonoOn φ (Icc x t₀) :=
            strictMonoOn_Icc_interior φ φ' x t₀ hcont_xt
              (fun y hy => hφd y ⟨by linarith [hy.1], by linarith [hy.2, ht₀.2, haμ]⟩)
              (fun y hy => hφpos y ⟨by linarith [hy.1], by linarith [hy.2, ht₀.2]⟩)
          have := hmono_xt ⟨le_refl x, hxt.le⟩ ⟨hxt.le, le_refl t₀⟩ hxt
          linarith [hφt₀]
        · -- t₀ ≤ x ≤ c: φ(x) ≤ φ(c) = 0  (φ mono on [t₀,a])
          have hxa : x ≤ a := le_of_lt (lt_of_le_of_lt hxc hca)
          rcases eq_or_lt_of_le hxc with hxceq | hxclt
          · rw [hxceq, hc_zero]
          · have hmono2 := hmono ⟨hxt, hxa⟩ ⟨ht₀c.le, hca.le⟩ hxclt
            rw [hc_zero] at hmono2; linarith
      have hle : f x ≤ f (2*μ - x) := (Real.log_le_log_iff hfx hf2).mp (by simpa [hφ_def] using hφx_le)
      linarith
  · -- g ≥ 0 on [c,μ]
    intro x hx
    rw [mem_Icc] at hx
    obtain ⟨hcx, hxμ⟩ := hx
    rcases eq_or_lt_of_le hxμ with hxeq | hxμ'
    · -- x = μ: g(μ) = f(μ)-f(μ) = 0
      rw [hxeq, show 2*μ - μ = μ by ring]; simp
    · have hx0 : 0 < x := lt_of_lt_of_le hc0 hcx
      have hfx : 0 < f x := hfpos x ⟨hx0, by linarith⟩
      have hf2 : 0 < f (2*μ - x) := hfpos (2*μ - x) ⟨by linarith, by linarith⟩
      have hφx_ge : 0 ≤ φ x := by
        rcases eq_or_lt_of_le hcx with hxceq | hcx'
        · rw [← hxceq, hc_zero]
        · -- x ∈ (c,μ): φ(x) ≥ 0. c ∈ (t₀,a). If x ≤ a use mono [c,a]; if x ≥ a use φ>0 on (a,μ).
          rcases lt_or_ge a x with hxa | hxa
          · -- a < x < μ: φ(x) > 0 directly
            have := hφpos_aμ x ⟨hxa, hxμ'⟩; linarith
          · -- c ≤ x ≤ a: φ(x) ≥ φ(c) = 0  (φ mono on [c,a])
            have hcont_ca : ContinuousOn φ (Icc c a) := by
              apply hφcont.mono; intro y hy; rw [mem_Icc] at hy; rw [mem_Ioc]
              exact ⟨by linarith, by linarith [haμ]⟩
            have hmono_ca : StrictMonoOn φ (Icc c a) :=
              strictMonoOn_Icc_interior φ φ' c a hcont_ca
                (fun y hy => hφd y ⟨by linarith [hc0, hy.1], by linarith [haμ, hy.2]⟩)
                (fun y hy => hφpos y ⟨by linarith [hc0, hy.1], hy.2⟩)
            have := hmono_ca ⟨le_refl c, hca.le⟩ ⟨hcx'.le, hxa⟩ hcx'
            rw [hc_zero] at this; linarith
      have hge : f (2*μ - x) ≤ f x := (Real.log_le_log_iff hf2 hfx).mp (by
        have : Real.log (f (2*μ-x)) - Real.log (f x) ≤ 0 := by simpa [hφ_def] using (by linarith [hφx_ge] : -(φ x) ≤ 0)
        linarith)
      linarith
