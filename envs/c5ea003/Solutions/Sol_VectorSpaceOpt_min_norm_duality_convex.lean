-- Prove2me | solution 1 for VectorSpaceOpt.min_norm_duality_convex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T13:35:01.734889+00:00
-- url     : https://prove2.me/submissions/07742fd6-47d2-4dd2-9e9c-369168c53fa1

import Mathlib
import Definitions.Def_VectorSpaceOpt_aligned
import Definitions.Def_VectorSpaceOpt_support_functional


theorem solution {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (K : Set X) (hK : Convex ℝ K) (hne : K.Nonempty)
    (x₁ : X) (hd : 0 < ⨅ x : K, ‖(x : X) - x₁‖) :
    ∃ f₀ : X →L[ℝ] ℝ, ‖f₀‖ ≤ 1 ∧
      ((f₀ x₁ : EReal) - VectorSpaceOpt_support_functional K f₀
        = ((⨅ x : K, ‖(x : X) - x₁‖ : ℝ) : EReal)) ∧
      (∀ f : X →L[ℝ] ℝ, ‖f‖ ≤ 1 →
        (f x₁ : EReal) - VectorSpaceOpt_support_functional K f
          ≤ ((⨅ x : K, ‖(x : X) - x₁‖ : ℝ) : EReal)) ∧
      (∀ x₀ ∈ K, ‖x₀ - x₁‖ = (⨅ x : K, ‖(x : X) - x₁‖) →
        VectorSpaceOpt_aligned (x₀ - x₁) (-f₀)) := by
  classical
  haveI : Nonempty K := hne.to_subtype
  -- the indexed infimum is the metric distance
  have hiInf : (⨅ x : K, ‖(x : X) - x₁‖) = Metric.infDist x₁ K := by
    rw [Metric.infDist_eq_iInf]
    exact iInf_congr fun x => by rw [dist_eq_norm, norm_sub_rev]
  set d : ℝ := Metric.infDist x₁ K with hdd
  rw [hiInf] at hd ⊢
  -- real weak duality
  have weak : ∀ (g : X →L[ℝ] ℝ) (b : ℝ), ‖g‖ ≤ 1 → (∀ k ∈ K, g k ≤ b) → g x₁ - b ≤ d := by
    intro g b hg hb
    rw [hdd]
    refine (Metric.le_infDist hne).2 fun k hk => ?_
    have h1 : g x₁ - g k ≤ ‖g (x₁ - k)‖ := by rw [map_sub]; exact le_abs_self _
    have h2 : ‖g (x₁ - k)‖ ≤ ‖g‖ * ‖x₁ - k‖ := g.le_opNorm _
    have h3 : ‖g‖ * ‖x₁ - k‖ ≤ ‖x₁ - k‖ := by
      have := norm_nonneg (x₁ - k); nlinarith
    have h4 := hb k hk
    rw [dist_eq_norm]
    linarith
  -- the support functional is never `⊥` on a nonempty set
  have hsupp_ne_bot : ∀ f : X →L[ℝ] ℝ, VectorSpaceOpt_support_functional K f ≠ ⊥ := by
    intro f hcon
    obtain ⟨k, hk⟩ := hne
    have : ((f k : ℝ) : EReal) ≤ VectorSpaceOpt_support_functional K f :=
      le_iSup (fun z : K => ((f (z : X) : ℝ) : EReal)) ⟨k, hk⟩
    rw [hcon, le_bot_iff] at this
    exact (EReal.coe_ne_bot _) this
  -- EReal weak duality
  have weakE : ∀ f : X →L[ℝ] ℝ, ‖f‖ ≤ 1 →
      (f x₁ : EReal) - VectorSpaceOpt_support_functional K f ≤ ((d : ℝ) : EReal) := by
    intro f hf
    rcases eq_or_ne (VectorSpaceOpt_support_functional K f) ⊤ with htop | htop
    · rw [htop, EReal.sub_top]; exact bot_le
    · set s : ℝ := (VectorSpaceOpt_support_functional K f).toReal with hs
      have hcoe : ((s : ℝ) : EReal) = VectorSpaceOpt_support_functional K f :=
        EReal.coe_toReal htop (hsupp_ne_bot f)
      have hbound : ∀ k ∈ K, f k ≤ s := by
        intro k hk
        have h1 : ((f k : ℝ) : EReal) ≤ VectorSpaceOpt_support_functional K f :=
          le_iSup (fun z : K => ((f (z : X) : ℝ) : EReal)) ⟨k, hk⟩
        rw [← hcoe] at h1
        exact_mod_cast h1
      have := weak f s hf hbound
      rw [← hcoe, ← EReal.coe_sub]
      exact_mod_cast this
  -- separate the open ball from `K`
  have hdisj : Disjoint (Metric.ball x₁ d) K := by
    rw [Set.disjoint_left]
    intro a ha haK
    have h1 : d ≤ dist x₁ a := by rw [hdd]; exact Metric.infDist_le_dist_of_mem haK
    have h2 : dist a x₁ < d := Metric.mem_ball.1 ha
    rw [dist_comm] at h1
    linarith
  obtain ⟨g, u, hgball, hgK⟩ :=
    geometric_hahn_banach_open (convex_ball x₁ d) Metric.isOpen_ball hK hdisj
  have hg0 : g ≠ 0 := by
    intro hzero
    obtain ⟨k, hk⟩ := hne
    have h1 : (0:ℝ) < u := by simpa [hzero] using hgball x₁ (Metric.mem_ball_self hd)
    have h2 : u ≤ (0:ℝ) := by simpa [hzero] using hgK k hk
    linarith
  have hgn : 0 < ‖g‖ := norm_pos_iff.2 hg0
  have hinv : (0:ℝ) < (‖g‖)⁻¹ := inv_pos.2 hgn
  have hkey : g x₁ + d * ‖g‖ ≤ u := by
    by_contra hcon
    push_neg at hcon
    have hr : (u - g x₁) / d < ‖g‖ := by rw [div_lt_iff₀ hd]; nlinarith
    obtain ⟨e, he1, he2⟩ := g.exists_lt_apply_of_lt_opNorm hr
    have hsign : ∃ e' : X, ‖e'‖ = ‖e‖ ∧ (u - g x₁) / d < g e' := by
      rcases le_or_gt 0 (g e) with h | h
      · exact ⟨e, rfl, by rwa [Real.norm_eq_abs, abs_of_nonneg h] at he2⟩
      · refine ⟨-e, by rw [norm_neg], ?_⟩
        rw [map_neg]
        rwa [Real.norm_eq_abs, abs_of_neg h] at he2
    obtain ⟨e', hn, hv⟩ := hsign
    have hmem : x₁ + d • e' ∈ Metric.ball x₁ d := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hd, hn]
      nlinarith [norm_nonneg e]
    have hlt := hgball _ hmem
    rw [map_add, map_smul, smul_eq_mul] at hlt
    have hstep : (u - g x₁) < d * g e' := by rw [← div_lt_iff₀' hd]; exact hv
    linarith
  set f₀ : X →L[ℝ] ℝ := (‖g‖)⁻¹ • (-g) with hf₀
  set c : ℝ := (‖g‖)⁻¹ * (-u) with hc
  have hfapp : ∀ w : X, f₀ w = (‖g‖)⁻¹ * (-(g w)) := by
    intro w
    rw [hf₀]
    simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply,
      ContinuousLinearMap.neg_apply, smul_eq_mul]
  have hfnorm : ‖f₀‖ = 1 := by
    rw [hf₀, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_pos hinv,
      inv_mul_cancel₀ (ne_of_gt hgn)]
  have hfK : ∀ k ∈ K, f₀ k ≤ c := by
    intro k hk
    have h := hgK k hk
    rw [hfapp k, hc]
    nlinarith
  have hfx : f₀ x₁ - c = d := by
    have hge : d ≤ f₀ x₁ - c := by
      rw [hfapp x₁, hc]
      have h1 : (‖g‖)⁻¹ * (u - g x₁) ≥ (‖g‖)⁻¹ * (d * ‖g‖) := by nlinarith
      have h2 : (‖g‖)⁻¹ * (d * ‖g‖) = d := by field_simp
      nlinarith
    have hle : f₀ x₁ - c ≤ d := weak f₀ c (le_of_eq hfnorm) hfK
    linarith
  -- the supremum of `f₀` over `K` is exactly `c`
  have hsupp : VectorSpaceOpt_support_functional K f₀ = ((c : ℝ) : EReal) := by
    refine le_antisymm ?_ ?_
    · refine iSup_le fun z => ?_
      exact_mod_cast hfK (z : X) z.2
    · by_contra hcon
      push_neg at hcon
      have htop : VectorSpaceOpt_support_functional K f₀ ≠ ⊤ := by
        intro h; rw [h] at hcon; exact absurd hcon (by simp)
      set s : ℝ := (VectorSpaceOpt_support_functional K f₀).toReal with hs
      have hcoe : ((s : ℝ) : EReal) = VectorSpaceOpt_support_functional K f₀ :=
        EReal.coe_toReal htop (hsupp_ne_bot f₀)
      have hbound : ∀ k ∈ K, f₀ k ≤ s := by
        intro k hk
        have h1 : ((f₀ k : ℝ) : EReal) ≤ VectorSpaceOpt_support_functional K f₀ :=
          le_iSup (fun z : K => ((f₀ (z : X) : ℝ) : EReal)) ⟨k, hk⟩
        rw [← hcoe] at h1
        exact_mod_cast h1
      have hws := weak f₀ s (le_of_eq hfnorm) hbound
      have hsc : s < c := by
        rw [← hcoe] at hcon
        exact_mod_cast hcon
      linarith
  refine ⟨f₀, le_of_eq hfnorm, ?_, weakE, ?_⟩
  · rw [hsupp, ← EReal.coe_sub]
    exact_mod_cast hfx
  · intro x₀ hx₀ hnorm
    rw [VectorSpaceOpt_aligned]
    have hnf : ‖-f₀‖ = 1 := by rw [norm_neg, hfnorm]
    have hlow : d ≤ (-f₀) (x₀ - x₁) := by
      rw [ContinuousLinearMap.neg_apply, map_sub]
      have := hfK x₀ hx₀
      linarith
    have hhigh : (-f₀) (x₀ - x₁) ≤ ‖-f₀‖ * ‖x₀ - x₁‖ := by
      calc (-f₀) (x₀ - x₁) ≤ ‖(-f₀) (x₀ - x₁)‖ := le_abs_self _
        _ ≤ ‖-f₀‖ * ‖x₀ - x₁‖ := (-f₀).le_opNorm _
    rw [hnf, one_mul, hnorm] at *
    linarith
