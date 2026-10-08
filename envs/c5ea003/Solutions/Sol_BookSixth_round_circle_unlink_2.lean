-- Prove2me | solution 2 for BookSixth.round_circle_unlink
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-04T14:02:39.201834+00:00
-- url     : https://prove2.me/submissions/74f03898-8eac-46cd-b1df-7844a8029f1b

import Mathlib
import Definitions.Def_BookSixth

/- Complete proof of BookSixth.round_circle_unlink.
The F494 tools are reproduced with attribution from Nickrobbins95,
accepted submission 2780f0aa-91c9-4124-a5f3-04378d618b46.
The subsequent BookCircleCompletion proofs implement the finite-family
hemisphere shrinking argument and ambient isotopy extension. -/

/- Source module: ReferenceTools -/
/- Adapted from Nickrobbins95, accepted Prove2Me submission 2780f0aa-91c9-4124-a5f3-04378d618b46. Exact helper proofs; no added axioms. -/

namespace F494

open BookSixth Matrix

def Reach (K E F : Set Space3) : Prop :=
  ∃ G : ℝ → Space3 ≃ₜ Space3,
    Continuous (fun p : ℝ × Space3 => G p.1 p.2) ∧
    Continuous (fun p : ℝ × Space3 => (G p.1).symm p.2) ∧
    (∀ x, G 0 x = x) ∧ (∀ t, ∀ x ∈ K, G t x = x) ∧ G 1 '' E = F

theorem reach_refl (K E : Set Space3) : Reach K E E :=
  ⟨fun _ => Homeomorph.refl Space3, by simpa using continuous_snd, by simpa using continuous_snd,
    fun _ => rfl, fun _ _ _ => rfl, by simp⟩

theorem reach_trans {K E F F' : Set Space3} (h1 : Reach K E F) (h2 : Reach K F F') :
    Reach K E F' := by
  obtain ⟨G, c1, d1, e1, k1, i1⟩ := h1
  obtain ⟨G', c2, d2, e2, k2, i2⟩ := h2
  refine ⟨fun t => (G t).trans (G' t), ?_, ?_, ?_, ?_, ?_⟩
  · exact c2.comp (continuous_fst.prodMk c1)
  · exact d1.comp (continuous_fst.prodMk d2)
  · intro x; simp [e1, e2]
  · intro t x hx; simp [k1 t x hx, k2 t x hx]
  · show ⇑((G 1).trans (G' 1)) '' E = F'
    rw [← i2, ← i1, ← Set.image_comp]; rfl

theorem lip_homeo (g : Space3 → Space3) (hg : ∀ x y, ‖g x - g y‖ ≤ 1 / 2 * ‖x - y‖) :
    ∃ Φ : Space3 ≃ₜ Space3, ∀ x, Φ x = x + g x := by
  have hA : ApproximatesLinearOn (fun x => x + g x)
      ((ContinuousLinearEquiv.refl ℝ Space3 : Space3 →L[ℝ] Space3)) Set.univ (1 / 2 : NNReal) := by
    intro x _ y _
    have : x + g x - (y + g y) - (ContinuousLinearEquiv.refl ℝ Space3 : Space3 →L[ℝ] Space3)
        (x - y) = g x - g y := by
      simp only [ContinuousLinearEquiv.coe_refl, ContinuousLinearMap.id_apply]; abel
    rw [this]
    simpa using hg x y
  refine ⟨hA.toHomeomorph _ (Or.inr ?_), fun x => rfl⟩
  have h1 : ‖((ContinuousLinearEquiv.refl ℝ Space3).symm : Space3 →L[ℝ] Space3)‖₊ = 1 := by
    rw [ContinuousLinearEquiv.refl_symm, ContinuousLinearEquiv.coe_refl]
    exact ContinuousLinearMap.nnnorm_id
  rw [h1, inv_one]
  rw [← NNReal.coe_lt_coe]; norm_num

theorem lip_isotopy (g : Space3 → Space3) (hgc : Continuous g)
    (hg : ∀ x y, ‖g x - g y‖ ≤ 1 / 2 * ‖x - y‖) :
    ∃ G : ℝ → Space3 ≃ₜ Space3, Continuous (fun p : ℝ × Space3 => G p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (G p.1).symm p.2) ∧
      ∀ t x, G t x = x + (max 0 (min t 1)) • g x := by
  set τ : ℝ → ℝ := fun t => max 0 (min t 1) with hτ
  have hτ0 : ∀ t, 0 ≤ τ t := fun t => le_max_left _ _
  have hτ1 : ∀ t, τ t ≤ 1 := fun t => max_le zero_le_one (min_le_right _ _)
  have hτl : ∀ t t', |τ t - τ t'| ≤ |t - t'| := by
    intro t t'
    calc |τ t - τ t'| = |max (min t 1) 0 - max (min t' 1) 0| := by simp only [hτ, max_comm]
      _ ≤ |min t 1 - min t' 1| := abs_max_sub_max_le_abs _ _ _
      _ ≤ max |t - t'| |1 - 1| := abs_min_sub_min_le_max _ _ _ _
      _ = |t - t'| := by simp
  have hgt : ∀ t, ∀ x y, ‖τ t • g x - τ t • g y‖ ≤ 1 / 2 * ‖x - y‖ := by
    intro t x y
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hτ0 t)]
    calc τ t * ‖g x - g y‖ ≤ 1 * ‖g x - g y‖ := by
          gcongr; exact hτ1 t
      _ ≤ 1 / 2 * ‖x - y‖ := by rw [one_mul]; exact hg x y
  choose Φ hΦ using fun t => lip_homeo (fun x => τ t • g x) (hgt t)
  refine ⟨Φ, ?_, ?_, fun t x => hΦ t x⟩
  · have : (fun p : ℝ × Space3 => Φ p.1 p.2) = fun p => p.2 + τ p.1 • g p.2 := by
      funext p; exact hΦ _ _
    rw [this]; fun_prop
  · rw [continuous_iff_continuousAt]
    rintro ⟨t0, y0⟩
    rw [Metric.continuousAt_iff]
    intro ε hε
    set x0 := (Φ t0).symm y0 with hx0def
    set Cg := ‖g x0‖ with hCg
    have hCg0 : 0 ≤ Cg := norm_nonneg _
    refine ⟨ε / (2 * (Cg + 1) + 1), by positivity, ?_⟩
    rintro ⟨t, y⟩ hd
    simp only at hd ⊢
    rw [Prod.dist_eq, max_lt_iff] at hd
    obtain ⟨hdt, hdy⟩ := hd
    simp only [Real.dist_eq] at hdt
    set x := (Φ t).symm y with hxdef
    have hx : x + τ t • g x = y := by rw [← hΦ]; exact (Φ t).apply_symm_apply y
    have hx0 : x0 + τ t0 • g x0 = y0 := by rw [← hΦ]; exact (Φ t0).apply_symm_apply y0
    have key : x - x0 = (y - y0) - (τ t • g x - τ t • g x0) - (τ t - τ t0) • g x0 := by
      rw [← hx, ← hx0, sub_smul]; abel
    have hn : ‖x - x0‖ ≤ ‖y - y0‖ + 1 / 2 * ‖x - x0‖ + |τ t - τ t0| * Cg := by
      calc ‖x - x0‖ = ‖(y - y0) - (τ t • g x - τ t • g x0) - (τ t - τ t0) • g x0‖ := by
            rw [key]
        _ ≤ ‖(y - y0) - (τ t • g x - τ t • g x0)‖ + ‖(τ t - τ t0) • g x0‖ := norm_sub_le _ _
        _ ≤ ‖y - y0‖ + ‖τ t • g x - τ t • g x0‖ + ‖(τ t - τ t0) • g x0‖ := by
          gcongr; exact norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          · exact hgt t x x0
          · rw [norm_smul, Real.norm_eq_abs]
    have h1 : |τ t - τ t0| ≤ |t - t0| := hτl t t0
    rw [dist_eq_norm] at hdy ⊢
    have hδ : ε / (2 * (Cg + 1) + 1) * (2 * (Cg + 1) + 1) = ε := by
      field_simp
    have hA : ‖x - x0‖ ≤ 2 * ‖y - y0‖ + 2 * |t - t0| * Cg := by nlinarith
    nlinarith [abs_nonneg (t - t0), norm_nonneg (y - y0)]


theorem step_reach (K U S : Set Space3) (ρ : ℝ) (hρ : 0 < ρ) (hUne : U.Nonempty)
    (hUK : ∀ k ∈ K, ρ ≤ Metric.infDist k U)
    (hSU : S ⊆ U) (B : Space3 → Space3) (hBc : Continuous B)
    (hBlip : ∀ y y', ‖(B y - y) - (B y' - y')‖ ≤ 1 / 4 * ‖y - y'‖)
    (hBsmall : ∀ y, Metric.infDist y U < ρ → ‖B y - y‖ ≤ ρ / 4) :
    Reach K S (B '' S) := by
  set β : Space3 → ℝ := fun y => max 0 (1 - Metric.infDist y U / ρ) with hβ
  have hβc : Continuous β := by
    have := Metric.continuous_infDist_pt (s := U)
    simp only [hβ]; fun_prop
  have hβ0 : ∀ y, 0 ≤ β y := fun y => le_max_left _ _
  have hβ1 : ∀ y, β y ≤ 1 := fun y => max_le zero_le_one (by
      have h1 := Metric.infDist_nonneg (x := y) (s := U)
      have : 0 ≤ Metric.infDist y U / ρ := div_nonneg h1 hρ.le
      linarith)
  have hβl : ∀ y y', |β y - β y'| ≤ ‖y - y'‖ / ρ := by
    intro y y'
    calc |β y - β y'| ≤ |(1 - Metric.infDist y U / ρ) - (1 - Metric.infDist y' U / ρ)| := by
          have := abs_max_sub_max_le_abs (1 - Metric.infDist y U / ρ)
            (1 - Metric.infDist y' U / ρ) 0
          simpa only [hβ, max_comm] using this
      _ = |Metric.infDist y U - Metric.infDist y' U| / ρ := by
          rw [show (1 - Metric.infDist y U / ρ) - (1 - Metric.infDist y' U / ρ)
            = (Metric.infDist y' U - Metric.infDist y U) / ρ by ring]
          rw [abs_div, abs_of_pos hρ, abs_sub_comm]
      _ ≤ ‖y - y'‖ / ρ := by
          gcongr
          rw [abs_le]
          have h1 := Metric.infDist_le_infDist_add_dist (x := y) (y := y') (s := U)
          have h2 := Metric.infDist_le_infDist_add_dist (x := y') (y := y) (s := U)
          rw [dist_eq_norm] at h1 h2
          rw [norm_sub_rev] at h2
          constructor <;> linarith
  have hβpos : ∀ y, β y ≠ 0 → Metric.infDist y U < ρ := by
    intro y hy
    by_contra hc'
    have hc : ρ ≤ Metric.infDist y U := not_lt.mp hc'
    apply hy
    simp only [hβ]
    apply max_eq_left
    have : 1 ≤ Metric.infDist y U / ρ := by rw [le_div_iff₀ hρ]; linarith
    linarith
  set g : Space3 → Space3 := fun y => β y • (B y - y) with hg
  have hgc : Continuous g := by simp only [hg]; fun_prop
  have hglip : ∀ y y', ‖g y - g y'‖ ≤ 1 / 2 * ‖y - y'‖ := by
    intro y y'
    by_cases hy' : β y' = 0
    · by_cases hy : β y = 0
      · simp only [hg, hy, hy', zero_smul, sub_self, norm_zero]; positivity
      · have hs := hBsmall y (hβpos y hy)
        have e : g y - g y' = β y' • ((B y - y) - (B y' - y')) + (β y - β y') • (B y - y) := by
          simp only [hg, smul_sub, sub_smul]; abel
        rw [e]
        calc _ ≤ ‖β y' • ((B y - y) - (B y' - y'))‖ + ‖(β y - β y') • (B y - y)‖ :=
              norm_add_le _ _
          _ = β y' * ‖(B y - y) - (B y' - y')‖ + |β y - β y'| * ‖B y - y‖ := by
              rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
                abs_of_nonneg (hβ0 y')]
          _ ≤ 1 * (1 / 4 * ‖y - y'‖) + (‖y - y'‖ / ρ) * (ρ / 4) := by
              apply add_le_add
              · exact mul_le_mul (hβ1 y') (hBlip y y') (norm_nonneg _) zero_le_one
              · exact mul_le_mul (hβl y y') hs (norm_nonneg _) (by positivity)
          _ = 1 / 2 * ‖y - y'‖ := by field_simp; ring
    · have hs := hBsmall y' (hβpos y' hy')
      have e : g y - g y' = β y • ((B y - y) - (B y' - y')) + (β y - β y') • (B y' - y') := by
        simp only [hg, smul_sub, sub_smul]; abel
      rw [e]
      calc _ ≤ ‖β y • ((B y - y) - (B y' - y'))‖ + ‖(β y - β y') • (B y' - y')‖ :=
            norm_add_le _ _
        _ = β y * ‖(B y - y) - (B y' - y')‖ + |β y - β y'| * ‖B y' - y'‖ := by
            rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
              abs_of_nonneg (hβ0 y)]
        _ ≤ 1 * (1 / 4 * ‖y - y'‖) + (‖y - y'‖ / ρ) * (ρ / 4) := by
            apply add_le_add
            · exact mul_le_mul (hβ1 y) (hBlip y y') (norm_nonneg _) zero_le_one
            · exact mul_le_mul (hβl y y') hs (norm_nonneg _) (by positivity)
        _ = 1 / 2 * ‖y - y'‖ := by field_simp; ring
  obtain ⟨G, hc, hci, hG⟩ := lip_isotopy g hgc hglip
  refine ⟨G, hc, hci, fun x => by simp [hG], fun t k hk => ?_, ?_⟩
  · have hb0 : β k = 0 := by
      simp only [hβ]
      apply max_eq_left
      have : 1 ≤ Metric.infDist k U / ρ := by rw [le_div_iff₀ hρ]; linarith [hUK k hk]
      linarith
    rw [hG]; simp [hg, hb0]
  · apply Set.image_congr
    intro y hy
    have hb1 : β y = 1 := by
      simp only [hβ, Metric.infDist_zero_of_mem (hSU hy), zero_div, sub_zero]
      norm_num
    rw [hG]; simp [hg, hb1]

theorem mulVec_bound (Q : Matrix (Fin 3) (Fin 3) ℝ) (ε : ℝ) (hQ : ∀ i j, |Q i j| ≤ ε)
    (w : Space3) : ‖Q *ᵥ w‖ ≤ 3 * ε * ‖w‖ := by
  have hε : 0 ≤ ε := le_trans (abs_nonneg _) (hQ 0 0)
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro i
  rw [Real.norm_eq_abs]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  have hw : ∀ j, |w j| ≤ ‖w‖ := fun j => by rw [← Real.norm_eq_abs]; exact norm_le_pi_norm w j
  calc |Q i 0 * w 0 + Q i 1 * w 1 + Q i 2 * w 2|
      ≤ |Q i 0 * w 0| + |Q i 1 * w 1| + |Q i 2 * w 2| := abs_add_three _ _ _
    _ = |Q i 0| * |w 0| + |Q i 1| * |w 1| + |Q i 2| * |w 2| := by simp [abs_mul]
    _ ≤ ε * ‖w‖ + ε * ‖w‖ + ε * ‖w‖ := by
        apply add_le_add (add_le_add _ _) _ <;>
          exact mul_le_mul (hQ _ _) (hw _) (abs_nonneg _) hε
    _ = 3 * ε * ‖w‖ := by ring


theorem T_reach (K E : Set Space3) (hK : IsClosed K) (hE : IsCompact E) (hEne : E.Nonempty)
    (M : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (b : ℝ → Space3) (hM : Continuous M) (hb : Continuous b)
    (hdet : ∀ s ∈ Set.Icc (0:ℝ) 1, (M s).det ≠ 0)
    (h0 : ∀ x ∈ E, M 0 *ᵥ x + b 0 = x)
    (havoid : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ x ∈ E, M s *ᵥ x + b s ∉ K) :
    Reach K E ((fun x => M 1 *ᵥ x + b 1) '' E) := by
  set A : ℝ → Space3 → Space3 := fun s x => M s *ᵥ x + b s with hA
  have hAc : Continuous (fun p : ℝ × Space3 => A p.1 p.2) := by
    simp only [hA]
    exact ((hM.comp continuous_fst).matrix_mulVec continuous_snd).add (hb.comp continuous_fst)
  set I01 := Set.Icc (0:ℝ) 1 with hI01
  set U := (fun p : ℝ × Space3 => A p.1 p.2) '' (I01 ×ˢ E) with hU
  have hUc : IsCompact U := (isCompact_Icc.prod hE).image hAc
  have hUne : U.Nonempty :=
    ⟨A 0 hEne.some, ⟨(0, hEne.some), ⟨⟨le_refl _, zero_le_one⟩, hEne.some_mem⟩, rfl⟩⟩
  have hUK : ∀ u ∈ U, u ∉ K := by
    rintro u ⟨⟨s, x⟩, ⟨hs, hx⟩, rfl⟩; exact havoid s hs x hx
  obtain ⟨ρ, hρ, hρK⟩ : ∃ ρ > 0, ∀ k ∈ K, ρ ≤ Metric.infDist k U := by
    rcases K.eq_empty_or_nonempty with hKe | hKne
    · exact ⟨1, one_pos, by simp [hKe]⟩
    · obtain ⟨u0, hu0, hmin⟩ :=
        hUc.exists_isMinOn hUne (Metric.continuous_infDist_pt (s := K)).continuousOn
      have hpos : 0 < Metric.infDist u0 K := (hK.notMem_iff_infDist_pos hKne).1 (hUK u0 hu0)
      refine ⟨Metric.infDist u0 K, hpos, fun k hk => ?_⟩
      rw [Metric.le_infDist hUne]
      intro u hu
      calc Metric.infDist u0 K ≤ Metric.infDist u K := hmin hu
        _ ≤ dist u k := Metric.infDist_le_dist_of_mem hk
        _ = dist k u := dist_comm _ _
  obtain ⟨R0, hR0⟩ := hUc.isBounded.exists_norm_le
  set R := max R0 0 + ρ with hRdef
  have hR : 0 ≤ R := by positivity
  have hnearR : ∀ y, Metric.infDist y U < ρ → ‖y‖ ≤ R := by
    intro y hy
    obtain ⟨u, hu, hdu⟩ := (Metric.infDist_lt_iff hUne).1 hy
    have := hR0 u hu
    rw [dist_eq_norm] at hdu
    calc ‖y‖ = ‖(y - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - u‖ + ‖u‖ := norm_add_le _ _
      _ ≤ R := by simp only [hRdef]; linarith [le_max_left R0 0]
  set κ : ℝ → ℝ := fun s => max 0 (min s 1) with hκ
  have hκI : ∀ s, κ s ∈ I01 := fun s => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hκid : ∀ s ∈ I01, κ s = s := fun s hs => by
    simp only [hκ, min_eq_left hs.2, max_eq_right hs.1]
  set N : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun s => (M (κ s))⁻¹ with hN
  have hNc : Continuous N := by
    have hon : ContinuousOn (fun s => (M s)⁻¹) I01 := by
      intro s hs
      apply ContinuousAt.continuousWithinAt
      refine (continuousAt_matrix_inv (M s) ?_).comp hM.continuousAt
      rw [Ring.inverse_eq_inv']
      exact continuousAt_inv₀ (hdet s hs)
    exact hon.comp_continuous (by fun_prop) hκI
  have hMN : ∀ s ∈ I01, M s * N s = 1 := fun s hs => by
    simp only [hN, hκid s hs]; exact Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet s hs))
  have hNM : ∀ s ∈ I01, N s * M s = 1 := fun s hs => by
    simp only [hN, hκid s hs]; exact Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet s hs))
  set Bm : ℝ → ℝ → Space3 → Space3 := fun s s' y => M s' *ᵥ (N s *ᵥ (y - b s)) + b s' with hBm
  have hBA : ∀ s ∈ I01, ∀ s' x, Bm s s' (A s x) = A s' x := by
    intro s hs s' x
    simp only [hBm, hA, add_sub_cancel_right, Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc, hNM s hs, Matrix.mul_one]
  have hBform : ∀ s s' y, Bm s s' y - y
      = (M s' * N s - 1) *ᵥ y + (b s' - (M s' * N s) *ᵥ b s) := by
    intro s s' y
    simp only [hBm, Matrix.mulVec_mulVec, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.one_mulVec]
    abel
  set Ψ : ℝ × ℝ → (Fin 3 → Fin 3 → ℝ) × Space3 :=
    fun p => (fun i j => (M p.2 * N p.1) i j, b p.2 - (M p.2 * N p.1) *ᵥ b p.1) with hΨ
  have hΨc : Continuous Ψ := by
    have hQ : Continuous (fun p : ℝ × ℝ => M p.2 * N p.1) :=
      (hM.comp continuous_snd).matrix_mul (hNc.comp continuous_fst)
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun i => continuous_pi fun j => hQ.matrix_elem i j
    · exact (hb.comp continuous_snd).sub (hQ.matrix_mulVec (hb.comp continuous_fst))
  have hUC := (isCompact_Icc.prod isCompact_Icc).uniformContinuousOn_of_continuous
    (s := I01 ×ˢ I01) hΨc.continuousOn
  rw [Metric.uniformContinuousOn_iff] at hUC
  set ε : ℝ := min (1 / 12) (ρ / (4 * (3 * R + 1))) with hε
  have hεpos : 0 < ε := lt_min (by norm_num) (by positivity)
  obtain ⟨η, hη, hηspec⟩ := hUC ε hεpos
  have hstep : ∀ s ∈ I01, ∀ s' ∈ I01, |s' - s| < η →
      Reach K (A s '' E) (A s' '' E) := by
    intro s hs s' hs' hss
    have hd := hηspec (s, s') ⟨hs, hs'⟩ (s, s) ⟨hs, hs⟩ (by
      rw [Prod.dist_eq]; simp only [dist_self, Real.dist_eq]
      rw [max_eq_right (abs_nonneg _)]; exact hss)
    have hΨd : Ψ (s, s) = (fun i j => (1 : Matrix (Fin 3) (Fin 3) ℝ) i j, 0) := by
      simp only [hΨ, hMN s hs, Matrix.one_mulVec, sub_self]
    rw [hΨd, Prod.dist_eq, max_lt_iff] at hd
    obtain ⟨hdQ, hdq⟩ := hd
    have hQe : ∀ i j, |(M s' * N s - 1) i j| ≤ ε := by
      intro i j
      have := (dist_le_pi_dist _ _ j).trans ((dist_le_pi_dist _ _ i).trans hdQ.le)
      simpa [Real.dist_eq, Matrix.sub_apply] using this
    have hqe : ‖b s' - (M s' * N s) *ᵥ b s‖ ≤ ε := by
      rw [dist_zero_right] at hdq; exact hdq.le
    have hε12 : ε ≤ 1 / 12 := min_le_left _ _
    have hεR : ε * (3 * R + 1) ≤ ρ / 4 := by
      calc ε * (3 * R + 1) ≤ ρ / (4 * (3 * R + 1)) * (3 * R + 1) := by
            gcongr; exact min_le_right _ _
        _ = ρ / 4 := by field_simp
    have hlin : ∀ w, ‖(M s' * N s - 1) *ᵥ w‖ ≤ 1 / 4 * ‖w‖ := by
      intro w
      calc _ ≤ 3 * ε * ‖w‖ := mulVec_bound _ ε hQe w
        _ ≤ 1 / 4 * ‖w‖ := by gcongr; linarith
    have h := step_reach K U (A s '' E) ρ hρ hUne hρK
      (by rintro _ ⟨x, hx, rfl⟩; exact ⟨(s, x), ⟨hs, hx⟩, rfl⟩) (Bm s s')
      (by simp only [hBm]; fun_prop)
      (by
        intro y y'
        rw [hBform, hBform]
        have : (M s' * N s - 1) *ᵥ y + (b s' - (M s' * N s) *ᵥ b s)
            - ((M s' * N s - 1) *ᵥ y' + (b s' - (M s' * N s) *ᵥ b s))
            = (M s' * N s - 1) *ᵥ (y - y') := by rw [Matrix.mulVec_sub]; abel
        rw [this]; exact hlin _)
      (by
        intro y hy
        rw [hBform]
        have h1 : ‖(M s' * N s - 1) *ᵥ y‖ ≤ 3 * ε * R :=
          (mulVec_bound _ ε hQe y).trans (by gcongr; exact hnearR y hy)
        calc _ ≤ ‖(M s' * N s - 1) *ᵥ y‖ + ‖b s' - (M s' * N s) *ᵥ b s‖ := norm_add_le _ _
          _ ≤ 3 * ε * R + ε := add_le_add h1 hqe
          _ ≤ ρ / 4 := by nlinarith)
    have himg : Bm s s' '' (A s '' E) = A s' '' E := by
      rw [← Set.image_comp]; exact Set.image_congr (fun x _ => hBA s hs s' x)
    rw [himg] at h; exact h
  have hind : ∀ k : ℕ, Reach K E (A (min 1 (k * (η / 2))) '' E) := by
    intro k
    induction k with
    | zero =>
      have : A (min 1 (((0:ℕ):ℝ) * (η / 2))) '' E = E := by
        rw [Nat.cast_zero, zero_mul, min_eq_right zero_le_one]
        ext y; constructor
        · rintro ⟨x, hx, rfl⟩; show M 0 *ᵥ x + b 0 ∈ E; rw [h0 x hx]; exact hx
        · intro hy; exact ⟨y, hy, h0 y hy⟩
      rw [this]; exact reach_refl K E
    | succ k ih =>
      refine reach_trans ih (hstep _ ⟨le_min zero_le_one
        (mul_nonneg (Nat.cast_nonneg _) (half_pos hη).le), min_le_left _ _⟩ _
        ⟨le_min zero_le_one (mul_nonneg (Nat.cast_nonneg _) (half_pos hη).le),
          min_le_left _ _⟩ ?_)
      calc |min 1 (((k + 1 : ℕ) : ℝ) * (η / 2)) - min 1 ((k : ℝ) * (η / 2))|
          ≤ max |1 - 1| |((k + 1 : ℕ) : ℝ) * (η / 2) - (k : ℝ) * (η / 2)| :=
            abs_min_sub_min_le_max _ _ _ _
        _ = η / 2 := by
            push_cast
            rw [show ((k:ℝ) + 1) * (η / 2) - (k : ℝ) * (η / 2) = η / 2 by ring]
            rw [sub_self, abs_zero, abs_of_pos (half_pos hη)]
            exact max_eq_right (half_pos hη).le
        _ < η := half_lt_self hη
  obtain ⟨k, hk⟩ := exists_nat_gt (2 / η)
  have hk1 : min 1 ((k : ℝ) * (η / 2)) = 1 := by
    apply min_eq_left
    have : 2 / η * (η / 2) = 1 := by field_simp
    nlinarith
  have := hind k
  rw [hk1] at this
  exact this


theorem T_range (K : Set Space3) (hK : IsClosed K) (f : ℝ → Space3) (hf : Continuous f)
    (hfp : ∀ t, f (t + 2 * Real.pi) = f t)
    (M : ℝ → Matrix (Fin 3) (Fin 3) ℝ) (b : ℝ → Space3) (hM : Continuous M) (hb : Continuous b)
    (hdet : ∀ s ∈ Set.Icc (0:ℝ) 1, (M s).det ≠ 0) (hM0 : M 0 = 1) (hb0 : b 0 = 0)
    (havoid : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t, M s *ᵥ f t + b s ∉ K)
    (g : ℝ → Space3) (hg : ∀ t, M 1 *ᵥ f t + b 1 = g t) :
    Reach K (Set.range f) (Set.range g) := by
  have hcomp : IsCompact (Set.range f) :=
    Function.Periodic.compact_of_continuous (c := 2 * Real.pi) (fun t => hfp t)
      (by positivity) hf
  have h := T_reach K (Set.range f) hK hcomp (Set.range_nonempty f) M b hM hb hdet
    (by rintro _ ⟨t, rfl⟩; simp [hM0, hb0])
    (by rintro s hs _ ⟨t, rfl⟩; exact havoid s hs t)
  have : (fun x => M 1 *ᵥ x + b 1) '' Set.range f = Set.range g := by
    rw [← Set.range_comp]; congr 1; funext t; exact hg t
  rw [this] at h; exact h

noncomputable def R01 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, -Real.sin θ, 0; Real.sin θ, Real.cos θ, 0; 0, 0, 1]
noncomputable def R02 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![Real.cos θ, 0, -Real.sin θ; 0, 1, 0; Real.sin θ, 0, Real.cos θ]
noncomputable def R12 (θ : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, 0, 0; 0, Real.cos θ, -Real.sin θ; 0, Real.sin θ, Real.cos θ]

theorem R01_mulVec (θ : ℝ) (x : Space3) : R01 θ *ᵥ x =
    ![Real.cos θ * x 0 - Real.sin θ * x 1, Real.sin θ * x 0 + Real.cos θ * x 1, x 2] := by
  funext i; fin_cases i <;> simp [R01, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem R02_mulVec (θ : ℝ) (x : Space3) : R02 θ *ᵥ x =
    ![Real.cos θ * x 0 - Real.sin θ * x 2, x 1, Real.sin θ * x 0 + Real.cos θ * x 2] := by
  funext i; fin_cases i <;> simp [R02, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem R12_mulVec (θ : ℝ) (x : Space3) : R12 θ *ᵥ x =
    ![x 0, Real.cos θ * x 1 - Real.sin θ * x 2, Real.sin θ * x 1 + Real.cos θ * x 2] := by
  funext i; fin_cases i <;> simp [R12, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;> ring

theorem R01_det (θ : ℝ) : (R01 θ).det = 1 := by
  simp [R01, Matrix.det_fin_three]; nlinarith [Real.cos_sq_add_sin_sq θ]
theorem R02_det (θ : ℝ) : (R02 θ).det = 1 := by
  simp [R02, Matrix.det_fin_three]; nlinarith [Real.cos_sq_add_sin_sq θ]
theorem R12_det (θ : ℝ) : (R12 θ).det = 1 := by
  simp [R12, Matrix.det_fin_three]; nlinarith [Real.cos_sq_add_sin_sq θ]

theorem R01_zero : R01 0 = 1 := by
  simp [R01, Matrix.one_fin_three]
theorem R02_zero : R02 0 = 1 := by
  simp [R02, Matrix.one_fin_three]
theorem R12_zero : R12 0 = 1 := by
  simp [R12, Matrix.one_fin_three]

theorem R01_cont (θ : ℝ) : Continuous (fun s : ℝ => R01 (s * θ)) := by
  apply continuous_matrix; intro i j
  fin_cases i <;> fin_cases j <;> simp [R01] <;> fun_prop
theorem R02_cont (θ : ℝ) : Continuous (fun s : ℝ => R02 (s * θ)) := by
  apply continuous_matrix; intro i j
  fin_cases i <;> fin_cases j <;> simp [R02] <;> fun_prop
theorem R12_cont (θ : ℝ) : Continuous (fun s : ℝ => R12 (s * θ)) := by
  apply continuous_matrix; intro i j
  fin_cases i <;> fin_cases j <;> simp [R12] <;> fun_prop

def sumsq (x : Space3) : ℝ := x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2

theorem sumsq_R01 (θ : ℝ) (x : Space3) : sumsq (R01 θ *ᵥ x) = sumsq x := by
  rw [R01_mulVec]; simp [sumsq]
  linear_combination (x 0 ^ 2 + x 1 ^ 2) * Real.cos_sq_add_sin_sq θ
theorem sumsq_R02 (θ : ℝ) (x : Space3) : sumsq (R02 θ *ᵥ x) = sumsq x := by
  rw [R02_mulVec]; simp [sumsq]
  linear_combination (x 0 ^ 2 + x 2 ^ 2) * Real.cos_sq_add_sin_sq θ
theorem sumsq_R12 (θ : ℝ) (x : Space3) : sumsq (R12 θ *ᵥ x) = sumsq x := by
  rw [R12_mulVec]; simp [sumsq]
  linear_combination (x 1 ^ 2 + x 2 ^ 2) * Real.cos_sq_add_sin_sq θ


theorem angle_57b (a b : ℝ) :
    ∃ θ : ℝ, Real.sin θ * a + Real.cos θ * b = 0 ∧ 0 ≤ Real.cos θ * a - Real.sin θ * b := by
  by_cases h : a = 0 ∧ b = 0
  · refine ⟨0, ?_, ?_⟩ <;> simp [h.1, h.2]
  · have hz : (⟨a, b⟩ : ℂ) ≠ 0 := by
      intro hz
      apply h
      exact ⟨congrArg Complex.re hz, congrArg Complex.im hz⟩
    refine ⟨-Complex.arg ⟨a, b⟩, ?_, ?_⟩
    · rw [Real.sin_neg, Real.cos_neg, Complex.sin_arg, Complex.cos_arg hz]
      simp only
      ring
    · rw [Real.sin_neg, Real.cos_neg, Complex.sin_arg, Complex.cos_arg hz]
      simp only
      have : 0 ≤ (a * a + b * b) / ‖(⟨a, b⟩ : ℂ)‖ :=
        div_nonneg (by nlinarith [mul_self_nonneg a, mul_self_nonneg b]) (norm_nonneg _)
      calc (0 : ℝ) ≤ (a * a + b * b) / ‖(⟨a, b⟩ : ℂ)‖ := this
        _ = _ := by ring

theorem frame57 (u v : Space3) (hu : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1)
    (hv : v 0 * v 0 + v 1 * v 1 + v 2 * v 2 = 1) (huv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0) :
    ∃ θ1 θ2 θ3 : ℝ, ∀ t : ℝ,
      R12 θ3 *ᵥ (R02 θ2 *ᵥ (R01 θ1 *ᵥ (Real.cos t • u + Real.sin t • v)))
        = ![Real.cos t, Real.sin t, 0] := by
  obtain ⟨θ1, h1a, h1b⟩ := angle_57b (u 0) (u 1)
  obtain ⟨θ2, h2a, h2b⟩ := angle_57b (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) (u 2)
  obtain ⟨θ3, h3a, h3b⟩ := angle_57b (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
      (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2)
  have p1 : (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) ^ 2
      + (Real.sin θ1 * u 0 + Real.cos θ1 * u 1) ^ 2 = u 0 ^ 2 + u 1 ^ 2 := by
    linear_combination (u 0 ^ 2 + u 1 ^ 2) * Real.cos_sq_add_sin_sq θ1
  have p2 : (Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2) ^ 2
      + (Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2) ^ 2
      = (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) ^ 2 + u 2 ^ 2 := by
    linear_combination ((Real.cos θ1 * u 0 - Real.sin θ1 * u 1) ^ 2 + u 2 ^ 2)
      * Real.cos_sq_add_sin_sq θ2
  have hρ2sq : (Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2) ^ 2
      = 1 := by
    linear_combination p2 + p1 + hu
      - (Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2) * h2a
      - (Real.sin θ1 * u 0 + Real.cos θ1 * u 1) * h1a
  have hρ2 : Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2 = 1 := by
    have hm : ((Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2) - 1)
        * ((Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2) + 1)
        = 0 := by linear_combination hρ2sq
    rcases mul_eq_zero.1 hm with h | h
    · linarith
    · linarith
  have q1 : (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
      + (Real.sin θ1 * u 0 + Real.cos θ1 * u 1) * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
      = u 0 * v 0 + u 1 * v 1 := by
    linear_combination (u 0 * v 0 + u 1 * v 1) * Real.cos_sq_add_sin_sq θ1
  have q2 : (Real.cos θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) - Real.sin θ2 * u 2)
        * (Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2)
      + (Real.sin θ2 * (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) + Real.cos θ2 * u 2)
        * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2)
      = (Real.cos θ1 * u 0 - Real.sin θ1 * u 1) * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
        + u 2 * v 2 := by
    linear_combination ((Real.cos θ1 * u 0 - Real.sin θ1 * u 1)
      * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + u 2 * v 2) * Real.cos_sq_add_sin_sq θ2
  have hd0 : Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2 = 0 := by
    linear_combination q2 + q1 + huv
      - (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2) * h2a
      - (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) * h1a
      - (Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2) * hρ2
  have p1v : (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) ^ 2
      + (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    linear_combination (v 0 ^ 2 + v 1 ^ 2) * Real.cos_sq_add_sin_sq θ1
  have p2v : (Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2) ^ 2
      + (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2) ^ 2
      = (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) ^ 2 + v 2 ^ 2 := by
    linear_combination ((Real.cos θ1 * v 0 - Real.sin θ1 * v 1) ^ 2 + v 2 ^ 2)
      * Real.cos_sq_add_sin_sq θ2
  have p3 : (Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) ^ 2
      + (Real.sin θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        + Real.cos θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) ^ 2
      = (Real.sin θ1 * v 0 + Real.cos θ1 * v 1) ^ 2
        + (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2) ^ 2 := by
    linear_combination ((Real.sin θ1 * v 0 + Real.cos θ1 * v 1) ^ 2
        + (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) + Real.cos θ2 * v 2) ^ 2)
      * Real.cos_sq_add_sin_sq θ3
  have hρ3sq : (Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) ^ 2 = 1 := by
    linear_combination p3 + p2v + p1v + hv
      - (Real.sin θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        + Real.cos θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) * h3a
      - (Real.cos θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1) - Real.sin θ2 * v 2) * hd0
  have hρ3 : Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2) = 1 := by
    have hm : ((Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) - 1) * ((Real.cos θ3 * (Real.sin θ1 * v 0 + Real.cos θ1 * v 1)
        - Real.sin θ3 * (Real.sin θ2 * (Real.cos θ1 * v 0 - Real.sin θ1 * v 1)
          + Real.cos θ2 * v 2)) + 1) = 0 := by linear_combination hρ3sq
    rcases mul_eq_zero.1 hm with h | h
    · linarith
    · linarith
  refine ⟨θ1, θ2, θ3, fun t => ?_⟩
  rw [R01_mulVec, R02_mulVec, R12_mulVec]
  funext i
  fin_cases i <;> simp
  · linear_combination Real.cos t * hρ2 + Real.sin t * hd0
  · linear_combination Real.cos t * (Real.cos θ3 * h1a - Real.sin θ3 * h2a)
      + Real.sin t * hρ3
  · linear_combination Real.cos t * (Real.sin θ3 * h1a + Real.cos θ3 * h2a)
      + Real.sin t * h3a


theorem endgame (n : ℕ) (K : Set Space3) (hK : IsClosed K) (hKP : ∀ x ∈ K, x 2 = 0)
    (hKn : ∀ x ∈ K, x ∉ standardCircle n)
    (c u v : Space3) (ρ : ℝ) (hρ : 0 < ρ)
    (hu : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1)
    (hv : v 0 * v 0 + v 1 * v 1 + v 2 * v 2 = 1) (huv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0)
    (hc : ρ + 1 < |c 2|) :
    Reach K (Set.range fun t => c + ρ • (Real.cos t • u + Real.sin t • v))
      (standardCircle n) := by
  obtain ⟨θ1, θ2, θ3, hframe⟩ := frame57 u v hu hv huv
  set W : ℝ → Space3 := fun t => Real.cos t • u + Real.sin t • v with hW
  have hWn : ∀ t, sumsq (W t) = 1 := by
    intro t
    simp only [hW, sumsq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (Real.cos t) ^ 2 * hu + (Real.sin t) ^ 2 * hv
      + 2 * Real.cos t * Real.sin t * huv + Real.cos_sq_add_sin_sq t
  have hρi : 0 < ρ⁻¹ := inv_pos.mpr hρ
  set lf : ℝ → ℝ := fun s => 1 + s * (ρ⁻¹ - 1) with hlf
  set Rm : ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun s => R12 (s * θ3) * R02 (s * θ2) * R01 (s * θ1) with hRmdef
  set tgt : Space3 := ![3 * (n:ℝ), 0, c 2] with htgt
  set M : ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun s => lf s • Rm s with hMdef
  set b : ℝ → Space3 := fun s => c + s • (tgt - c) - M s *ᵥ c with hbdef
  have hRm : ∀ s x, Rm s *ᵥ x = R12 (s * θ3) *ᵥ (R02 (s * θ2) *ᵥ (R01 (s * θ1) *ᵥ x)) := by
    intro s x; simp only [hRmdef, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hsum : ∀ s x, sumsq (Rm s *ᵥ x) = sumsq x := by
    intro s x; rw [hRm, sumsq_R12, sumsq_R02, sumsq_R01]
  have hMf : ∀ s t, M s *ᵥ (c + ρ • W t) + b s
      = c + s • (tgt - c) + (lf s * ρ) • (Rm s *ᵥ W t) := by
    intro s t
    simp only [hMdef, hbdef, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]
    module
  have hlfpos : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 < lf s := by
    intro s hs
    simp only [hlf]
    rcases hs.2.lt_or_eq with h | h
    · nlinarith [mul_nonneg hs.1 hρi.le]
    · rw [h]; linarith
  have hRc : Continuous Rm :=
    ((R12_cont θ3).matrix_mul (R02_cont θ2)).matrix_mul (R01_cont θ1)
  have hMc : Continuous M := (by fun_prop : Continuous lf).smul hRc
  have hc2 : c 2 ≠ 0 := by
    intro h; rw [h, abs_zero] at hc; linarith
  have step1 := T_range K hK (fun t => c + ρ • W t) (by simp only [hW]; fun_prop)
    (fun t => by simp only [hW, Real.cos_add_two_pi, Real.sin_add_two_pi])
    M b hMc (by simp only [hbdef]; exact (continuous_const.add
      (continuous_id.smul continuous_const)).sub (hMc.matrix_mulVec continuous_const))
    (by
      intro s hs
      rw [hMdef]; simp only
      rw [Matrix.det_smul, Fintype.card_fin, hRmdef]; simp only
      rw [Matrix.det_mul, Matrix.det_mul, R12_det, R02_det, R01_det]
      have := hlfpos s hs
      positivity)
    (by
      simp only [hMdef, hRmdef, hlf, zero_mul, R12_zero, R02_zero, R01_zero, Matrix.mul_one,
        one_smul, add_zero])
    (by simp [hbdef, hMdef, hRmdef, hlf, R12_zero, R02_zero, R01_zero])
    (by
      intro s hs t hP
      have hz := hKP _ hP
      rw [hMf] at hz
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, htgt,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hz
      have hX := hsum s (W t)
      rw [hWn] at hX
      simp only [sumsq] at hX
      have hX2 : |(Rm s *ᵥ W t) 2| ≤ 1 := by
        rw [← sq_le_one_iff_abs_le_one]; nlinarith [sq_nonneg ((Rm s *ᵥ W t) 0),
          sq_nonneg ((Rm s *ᵥ W t) 1)]
      have hl0 := hlfpos s hs
      have hlr : lf s * ρ ≤ ρ + 1 := by
        simp only [hlf]
        rw [show (1 + s * (ρ⁻¹ - 1)) * ρ = ρ + s * (ρ⁻¹ * ρ - ρ) by ring,
          inv_mul_cancel₀ hρ.ne']
        rcases le_total ρ 1 with h | h
        · nlinarith [hs.1, hs.2]
        · nlinarith [hs.1, hs.2]
      have hkey : c 2 = -(lf s * ρ * (Rm s *ᵥ W t) 2) := by linear_combination hz
      have : |c 2| ≤ lf s * ρ := by
        rw [hkey, abs_neg, abs_mul, abs_of_pos (by positivity : 0 < lf s * ρ)]
        exact (mul_le_mul_of_nonneg_left hX2 (by positivity)).trans (le_of_eq (mul_one _))
      linarith)
    (fun t => ![3 * (n:ℝ) + Real.cos t, Real.sin t, c 2])
    (by
      intro t
      rw [hMf]
      have h1 : lf 1 * ρ = 1 := by simp only [hlf]; field_simp; ring
      rw [h1, one_smul, one_smul]
      have h2 : Rm 1 *ᵥ W t = ![Real.cos t, Real.sin t, 0] := by
        rw [hRm]; simp only [one_mul]; exact hframe t
      rw [h2]
      funext i; fin_cases i <;> simp [htgt])
  have step2 := T_range K hK (fun t => ![3 * (n:ℝ) + Real.cos t, Real.sin t, c 2])
    (by fun_prop) (fun t => by simp only [Real.cos_add_two_pi, Real.sin_add_two_pi])
    (fun _ => 1) (fun s => s • ![0, 0, -c 2]) continuous_const (by fun_prop)
    (by intro s _; simp) rfl (by simp)
    (by
      intro s hs t hP
      have hz := hKP _ hP
      simp at hz
      have hs1 : s = 1 := by
        have : (1 - s) * c 2 = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · linarith
        · exact absurd h hc2
      subst hs1
      apply hKn _ hP
      refine ⟨t, ?_⟩
      funext i; fin_cases i <;> simp)
    (fun t => ![3 * (n:ℝ) + Real.cos t, Real.sin t, 0])
    (by intro t; funext i; fin_cases i <;> simp)
  exact reach_trans step1 step2


-- ===== Part A =====

theorem lift_R2 (W : ℝ × ℝ → ℂ) (hW : Continuous W) (hne : ∀ p, W p ≠ 0) :
    ∃ F : ℝ × ℝ → ℂ, Continuous F ∧ ∀ p, Complex.exp (F p) = W p := by
  obtain ⟨F, ⟨_, hF⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    (⟨W, hW⟩ : C(ℝ × ℝ, ℂ)) (a₀ := ((0:ℝ), (0:ℝ))) (e₀ := Complex.log (W (0, 0)))
    (by simp [Complex.exp_log (hne _)]) (fun a => by simpa using hne a)
  exact ⟨F, F.continuous, fun p => congr_fun hF p⟩

theorem exp_lift_eq {A : Type*} [TopologicalSpace A] [PreconnectedSpace A] (g₁ g₂ : A → ℂ)
    (h₁ : Continuous g₁) (h₂ : Continuous g₂) (he : ∀ a, Complex.exp (g₁ a) = Complex.exp (g₂ a))
    (a : A) (ha : g₁ a = g₂ a) : g₁ = g₂ :=
  Complex.isCoveringMap_exp.eq_of_comp_eq h₁ h₂ (funext fun x => Subtype.ext (he x)) a ha

theorem exp_lift_const {A : Type*} [TopologicalSpace A] [PreconnectedSpace A] (g : A → ℂ)
    (hg : Continuous g) (he : ∀ a a', Complex.exp (g a) = Complex.exp (g a')) (a a' : A) :
    g a = g a' :=
  Complex.isCoveringMap_exp.const_of_comp hg (fun a a' => Subtype.ext (he a a')) a a'

/-- two continuous logs of the same function on ℝ have the same increments -/
theorem exp_lift_diff (Λ ℓ : ℝ → ℂ) (hΛ : Continuous Λ) (hℓ : Continuous ℓ)
    (he : ∀ t, Complex.exp (Λ t) = Complex.exp (ℓ t)) (a b : ℝ) :
    Λ b - Λ a = ℓ b - ℓ a := by
  have key := exp_lift_eq Λ (fun t => ℓ t + (Λ a - ℓ a)) hΛ (by fun_prop)
    (fun t => by
      rw [Complex.exp_add, Complex.exp_sub, he a, div_self (Complex.exp_ne_zero _), mul_one, he t])
    a (by ring)
  have := congr_fun key b
  simp only at this
  rw [this]; ring

/-- a nonvanishing map on ℝ×ℝ, periodic in t, constant in t at s = 1, gives a periodic log at s = 0 -/
theorem periodic_log (W : ℝ × ℝ → ℂ) (hW : Continuous W) (hne : ∀ p, W p ≠ 0)
    (hper : ∀ s t, W (s, t + 2 * Real.pi) = W (s, t)) (hconst : ∀ t, W (1, t) = W (1, 0)) :
    ∃ Λ : ℝ → ℂ, Continuous Λ ∧ (∀ t, Complex.exp (Λ t) = W (0, t)) ∧
      ∀ t, Λ (t + 2 * Real.pi) = Λ t := by
  obtain ⟨F, hF, hFe⟩ := lift_R2 W hW hne
  have hG : Continuous (fun p : ℝ × ℝ => F (p.1, p.2 + 2 * Real.pi)) := by fun_prop
  have h1 : ∀ t, F (1, t) = F (1, 0) := by
    intro t
    have := exp_lift_const (fun t : ℝ => F (1, t)) (by fun_prop)
      (fun a a' => by simp only [hFe, hconst a, hconst a']) t 0
    exact this
  have key := exp_lift_eq (fun p : ℝ × ℝ => F (p.1, p.2 + 2 * Real.pi))
    (fun p => F p + (F (1, 0 + 2 * Real.pi) - F (1, 0))) hG (by fun_prop)
    (fun p => by
      simp only [Complex.exp_add, Complex.exp_sub, hFe]
      rw [hper, hper, div_self (hne _), mul_one])
    (1, 0) (by simp)
  refine ⟨fun t => F (0, t), by fun_prop, fun t => hFe _, fun t => ?_⟩
  have := congr_fun key (0, t)
  simp only at this
  show F (0, t + 2 * Real.pi) = F (0, t)
  rw [this, h1 (0 + 2 * Real.pi)]
  ring

theorem exists_angle (a b : ℝ) (h : a ^ 2 + b ^ 2 = 1) :
    ∃ θ : ℝ, Real.cos θ = a ∧ Real.sin θ = b := by
  set z : ℂ := ⟨a, b⟩ with hz
  have hn : ‖z‖ = 1 := by
    rw [Complex.norm_def, Complex.normSq_mk]
    rw [show a * a + b * b = 1 by nlinarith [h]]
    simp
  have hz0 : z ≠ 0 := by
    intro h0; rw [h0] at hn; simp at hn
  refine ⟨Complex.arg z, ?_, ?_⟩
  · rw [Complex.cos_arg hz0, hn]; simp [hz]
  · rw [Complex.sin_arg, hn]; simp [hz]


theorem arg_negI_pos (x : ℝ) (hx : 0 < x) : Complex.arg (-Complex.I * (x : ℂ)) = -(Real.pi / 2) := by
  rw [show -Complex.I * (x : ℂ) = (x : ℂ) * (-Complex.I) by ring, Complex.arg_real_mul _ hx,
    Complex.arg_neg_I]

theorem arg_negI_neg (x : ℝ) (hx : x < 0) : Complex.arg (-Complex.I * (x : ℂ)) = Real.pi / 2 := by
  rw [show -Complex.I * (x : ℂ) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.arg_real_mul _ (by linarith), Complex.arg_I]

theorem arg_I_pos (x : ℝ) (hx : 0 < x) : Complex.arg (Complex.I * (x : ℂ)) = Real.pi / 2 := by
  rw [show Complex.I * (x : ℂ) = (x : ℂ) * Complex.I by ring, Complex.arg_real_mul _ hx,
    Complex.arg_I]

theorem arg_I_neg (x : ℝ) (hx : x < 0) : Complex.arg (Complex.I * (x : ℂ)) = -(Real.pi / 2) := by
  rw [show Complex.I * (x : ℂ) = ((-x : ℝ) : ℂ) * (-Complex.I) by push_cast; ring,
    Complex.arg_real_mul _ (by linarith), Complex.arg_neg_I]

theorem crossing_false (w Λ : ℝ → ℂ) (hw : Continuous w) (hΛ : Continuous Λ)
    (hexp : ∀ t, Complex.exp (Λ t) = w t) (hper : ∀ t, Λ (t + 2 * Real.pi) = Λ t)
    (t1 t2 : ℝ) (h12 : t1 ≤ t2) (h21 : t2 ≤ t1 + 2 * Real.pi)
    (hup : ∀ t, t1 ≤ t → t ≤ t2 → 0 ≤ (w t).im)
    (hdown : ∀ t, t2 ≤ t → t ≤ t1 + 2 * Real.pi → (w t).im ≤ 0)
    (h1 : (w t1).im = 0) (h2 : (w t2).im = 0)
    (hsign : (w t1).re * (w t2).re < 0) : False := by
  have hne : ∀ t, w t ≠ 0 := fun t => by rw [← hexp]; exact Complex.exp_ne_zero _
  set c1 : ℝ → ℝ := fun t => max t1 (min t t2) with hc1
  set c2 : ℝ → ℝ := fun t => max t2 (min t (t1 + 2 * Real.pi)) with hc2
  have hc1c : Continuous c1 := by fun_prop
  have hc2c : Continuous c2 := by fun_prop
  have hc1a : ∀ t, t1 ≤ c1 t ∧ c1 t ≤ t2 := fun t =>
    ⟨le_max_left _ _, max_le h12 (min_le_right _ _)⟩
  have hc2a : ∀ t, t2 ≤ c2 t ∧ c2 t ≤ t1 + 2 * Real.pi := fun t =>
    ⟨le_max_left _ _, max_le h21 (min_le_right _ _)⟩
  have slit1 : ∀ t, -Complex.I * w (c1 t) ∈ Complex.slitPlane := by
    intro t
    rw [Complex.mem_slitPlane_iff]
    have hi := hup (c1 t) (hc1a t).1 (hc1a t).2
    simp only [Complex.mul_re, Complex.neg_re, Complex.I_re, Complex.neg_im, Complex.I_im,
      Complex.mul_im]
    rcases hi.lt_or_eq with h | h
    · left; linarith
    · right
      intro hre
      apply hne (c1 t)
      apply Complex.ext
      · simp only [Complex.zero_re]; linarith
      · simp only [Complex.zero_im]; linarith
  have slit2 : ∀ t, Complex.I * w (c2 t) ∈ Complex.slitPlane := by
    intro t
    rw [Complex.mem_slitPlane_iff]
    have hi := hdown (c2 t) (hc2a t).1 (hc2a t).2
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.mul_im]
    rcases hi.lt_or_eq with h | h
    · left; linarith
    · right
      intro hre
      apply hne (c2 t)
      apply Complex.ext
      · simp only [Complex.zero_re]; linarith
      · simp only [Complex.zero_im]; linarith
  set ℓ1 : ℝ → ℂ := fun t => Complex.log (-Complex.I * w (c1 t)) + (Real.pi / 2 * Complex.I)
    with hℓ1
  set ℓ2 : ℝ → ℂ := fun t => Complex.log (Complex.I * w (c2 t)) + (-Real.pi / 2 * Complex.I)
    with hℓ2
  have hℓ1c : Continuous ℓ1 :=
    ((continuous_const.mul (hw.comp hc1c)).clog slit1).add continuous_const
  have hℓ2c : Continuous ℓ2 :=
    ((continuous_const.mul (hw.comp hc2c)).clog slit2).add continuous_const
  have e1 := exp_lift_diff (fun t => Λ (c1 t)) ℓ1 (hΛ.comp hc1c) hℓ1c (fun t => by
    simp only [hℓ1, Complex.exp_add, Complex.exp_log (by
      intro h0; exact Complex.slitPlane_ne_zero (slit1 t) h0), Complex.exp_pi_div_two_mul_I, hexp]
    ring_nf; rw [Complex.I_sq]; ring) t1 t2
  have e2 := exp_lift_diff (fun t => Λ (c2 t)) ℓ2 (hΛ.comp hc2c) hℓ2c (fun t => by
    simp only [hℓ2, Complex.exp_add, Complex.exp_log (by
      intro h0; exact Complex.slitPlane_ne_zero (slit2 t) h0), Complex.exp_neg_pi_div_two_mul_I,
      hexp]
    ring_nf; rw [Complex.I_sq]; ring) t2 (t1 + 2 * Real.pi)
  have ec1a : c1 t1 = t1 := by simp [hc1, h12]
  have ec1b : c1 t2 = t2 := by simp [hc1, h12]
  have ec2a : c2 t2 = t2 := by simp [hc2, h21]
  have ec2b : c2 (t1 + 2 * Real.pi) = t1 + 2 * Real.pi := by simp [hc2, h21]
  simp only [ec1a, ec1b, ec2a, ec2b] at e1 e2
  have hw1 : w t1 = ((w t1).re : ℂ) := by
    apply Complex.ext <;> simp [h1]
  have hw2 : w t2 = ((w t2).re : ℂ) := by
    apply Complex.ext <;> simp [h2]
  have hw3 : w (t1 + 2 * Real.pi) = ((w t1).re : ℂ) := by
    rw [← hexp, hper, hexp, hw1]
    simp
  have tot : (Λ (t1 + 2 * Real.pi) - Λ t1).im = 0 := by rw [hper]; simp
  have tot2 : Λ (t1 + 2 * Real.pi) - Λ t1 = (ℓ1 t2 - ℓ1 t1) + (ℓ2 (t1 + 2 * Real.pi) - ℓ2 t2) := by
    rw [← e1, ← e2]; ring
  rw [tot2] at tot
  simp only [hℓ1, hℓ2, ec1a, ec1b, ec2a, ec2b, Complex.sub_im, Complex.add_im,
    Complex.log_im, Complex.mul_im, Complex.I_re, Complex.I_im] at tot
  rw [hw1, hw2, hw3] at tot
  rcases lt_or_gt_of_ne (show (w t1).re ≠ 0 by intro h; rw [h] at hsign; simp at hsign) with ha | ha
  · have hb : 0 < (w t2).re := by nlinarith
    rw [arg_negI_neg _ ha, arg_negI_pos _ hb, arg_I_pos _ hb, arg_I_neg _ ha] at tot
    simp at tot
    try nlinarith [Real.pi_pos]
  · have hb : (w t2).re < 0 := by nlinarith
    rw [arg_negI_pos _ ha, arg_negI_neg _ hb, arg_I_neg _ hb, arg_I_pos _ ha] at tot
    simp at tot
    try nlinarith [Real.pi_pos]


noncomputable def fj (j : ℕ) (x : Space3) : ℂ :=
  (((x 0 - 3 * (j:ℝ)) ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 1 : ℝ) : ℂ) + ((2 * x 2 : ℝ) : ℂ) * Complex.I

theorem fj_continuous (j : ℕ) : Continuous (fj j) := by
  unfold fj; fun_prop

theorem fj_re (j : ℕ) (x : Space3) : (fj j x).re = (x 0 - 3 * (j:ℝ)) ^ 2 + x 1 ^ 2 + x 2 ^ 2 - 1 := by
  simp only [fj, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]; ring

theorem fj_im (j : ℕ) (x : Space3) : (fj j x).im = 2 * x 2 := by
  simp only [fj, Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]; ring

theorem fj_zero (j : ℕ) (x : Space3) (h : fj j x = 0) : x ∈ standardCircle j := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  rw [fj_re] at hre
  rw [fj_im] at him
  simp only [Complex.zero_re, Complex.zero_im] at hre him
  have hx2 : x 2 = 0 := by linarith
  obtain ⟨θ, hc, hs⟩ := exists_angle (x 0 - 3 * j) (x 1) (by rw [hx2] at hre; nlinarith)
  refine ⟨θ, ?_⟩
  funext i; fin_cases i <;> simp [hc, hs, hx2]

theorem std_x0_le (y : Space3) (hy : y ∈ standardCircle 0) : y 0 ≤ 1 := by
  obtain ⟨θ, rfl⟩ := hy
  simp [Real.cos_le_one]

theorem std_x0_ge (y : Space3) (hy : y ∈ standardCircle 1) : 2 ≤ y 0 := by
  obtain ⟨θ, rfl⟩ := hy
  simp only [Nat.cast_one, Matrix.cons_val_zero]
  linarith [Real.neg_one_le_cos θ]

theorem unlink_data (j : ℕ) (d : ℝ → Space3) (hd : Continuous d)
    (hdper : ∀ t, d (t + 2 * Real.pi) = d t)
    (hU : IsUnlink (![Set.range d, standardCircle j] : Fin 2 → Set Space3)) :
    (∀ t, d t ∉ standardCircle j) ∧
    ∃ Λ : ℝ → ℂ, Continuous Λ ∧ (∀ t, Complex.exp (Λ t) = fj j (d t)) ∧
      ∀ t, Λ (t + 2 * Real.pi) = Λ t := by
  obtain ⟨H, hc, hci, h0, h1⟩ := hU
  have hD : H 1 '' Set.range d = standardCircle 0 := by simpa using h1 0
  have hC : H 1 '' standardCircle j = standardCircle 1 := by simpa using h1 1
  have hmemD : ∀ t, H 1 (d t) ∈ standardCircle 0 := fun t => hD ▸ ⟨d t, ⟨t, rfl⟩, rfl⟩
  have hmemC : ∀ x ∈ standardCircle j, H 1 x ∈ standardCircle 1 := fun x hx => hC ▸ ⟨x, hx, rfl⟩
  refine ⟨fun t ht => ?_, ?_⟩
  · have := std_x0_ge _ (hmemC _ ht)
    have := std_x0_le _ (hmemD t)
    linarith
  set κ : ℝ → ℝ := fun s => max 0 (min s 1) with hκ
  have hκc : Continuous κ := by fun_prop
  have hκ0 : ∀ s, 0 ≤ κ s := fun s => le_max_left _ _
  have hκ1 : ∀ s, κ s ≤ 1 := fun s => max_le zero_le_one (min_le_right _ _)
  set Φ : ℝ × ℝ → Space3 := fun p => (H 1).symm ((1 - κ p.1) • H 1 (d p.2)) with hΦ
  have hΦc : Continuous Φ := by
    have h1c : Continuous (H 1) := (H 1).continuous
    have h2c : Continuous (H 1).symm := (H 1).symm.continuous
    exact h2c.comp ((continuous_const.sub (hκc.comp continuous_fst)).smul
      (h1c.comp (hd.comp continuous_snd)))
  have hΦC : ∀ p, Φ p ∉ standardCircle j := by
    intro p hp
    have hm := hmemC _ hp
    simp only [hΦ, Homeomorph.apply_symm_apply] at hm
    have h2 := std_x0_ge _ hm
    have h3 := std_x0_le _ (hmemD p.2)
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have := hκ0 p.1
    have := hκ1 p.1
    nlinarith
  obtain ⟨Λ, hΛc, hΛe, hΛp⟩ := periodic_log (fun p => fj j (Φ p)) ((fj_continuous j).comp hΦc)
    (fun p h => hΦC p (fj_zero j _ h))
    (fun s t => by simp only [hΦ, hdper])
    (fun t => by simp [hΦ, hκ])
  refine ⟨Λ, hΛc, fun t => ?_, hΛp⟩
  rw [hΛe]
  simp [hΦ, hκ]



-- ===== K facts =====
def Kset (n : ℕ) : Set Space3 := {x | ∃ j, j < n ∧ x ∈ standardCircle j}

theorem std_closed (j : ℕ) : IsClosed (standardCircle j) :=
  (Function.Periodic.compact_of_continuous (c := 2 * Real.pi)
    (fun t => by simp only [Real.cos_add_two_pi, Real.sin_add_two_pi]) (by positivity)
    (by fun_prop)).isClosed

theorem K_closed (n : ℕ) : IsClosed (Kset n) := by
  have : Kset n = ⋃ j : Fin n, standardCircle (j : ℕ) := by
    ext x; simp only [Kset, Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨j, hj, hx⟩; exact ⟨⟨j, hj⟩, hx⟩
    · rintro ⟨j, hx⟩; exact ⟨j, j.2, hx⟩
  rw [this]; exact isClosed_iUnion_of_finite (fun j => std_closed j)

theorem K_mem {n : ℕ} {x : Space3} (hx : x ∈ Kset n) :
    x 2 = 0 ∧ ∃ j, j < n ∧ ∃ θ : ℝ, x 0 = 3 * (j : ℝ) + Real.cos θ ∧ x 1 = Real.sin θ := by
  obtain ⟨j, hj, θ, hθ⟩ := hx
  subst hθ
  refine ⟨by simp, j, hj, θ, by simp, by simp⟩

theorem K_z {n : ℕ} {x : Space3} (hx : x ∈ Kset n) : x 2 = 0 := (K_mem hx).1

theorem K_x0 {n : ℕ} {x : Space3} (hx : x ∈ Kset n) : -1 ≤ x 0 := by
  obtain ⟨-, j, -, θ, h0, -⟩ := K_mem hx
  rw [h0]
  have : (0:ℝ) ≤ j := Nat.cast_nonneg j
  linarith [Real.neg_one_le_cos θ]

theorem K_x1 {n : ℕ} {x : Space3} (hx : x ∈ Kset n) : x 1 ^ 2 ≤ 1 := by
  obtain ⟨-, j, -, θ, -, h1⟩ := K_mem hx
  rw [h1]
  nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]

theorem K_circle {n : ℕ} {x : Space3} (hx : x ∈ Kset n) :
    ∃ j, j < n ∧ (x 0 - 3 * (j:ℝ)) ^ 2 + x 1 ^ 2 = 1 := by
  obtain ⟨-, j, hj, θ, h0, h1⟩ := K_mem hx
  refine ⟨j, hj, ?_⟩
  rw [h0, h1]
  nlinarith [Real.sin_sq_add_cos_sq θ]

theorem K_not_n {n : ℕ} {x : Space3} (hx : x ∈ Kset n) : x ∉ standardCircle n := by
  obtain ⟨-, j, hj, θ, h0, -⟩ := K_mem hx
  rintro ⟨φ, hφ⟩
  have e0 := congrFun hφ 0
  simp only [Matrix.cons_val_zero] at e0
  have hjn : (j : ℝ) + 1 ≤ n := by exact_mod_cast hj
  rw [h0] at e0
  nlinarith [Real.neg_one_le_cos θ, Real.cos_le_one φ, Real.cos_le_one θ, Real.neg_one_le_cos φ]

theorem disk_not_K {n : ℕ} (j : ℕ) (x : Space3) (h : (x 0 - 3 * (j:ℝ)) ^ 2 + x 1 ^ 2 < 1) :
    x ∉ Kset n := by
  intro hx
  obtain ⟨-, k, -, θ, h0, h1⟩ := K_mem hx
  rw [h0, h1] at h
  have hc := Real.sin_sq_add_cos_sq θ
  rcases lt_trichotomy k j with hkj | hkj | hkj
  · have : (k : ℝ) + 1 ≤ j := by exact_mod_cast hkj
    nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, sq_nonneg (Real.sin θ)]
  · subst hkj; nlinarith
  · have : (j : ℝ) + 1 ≤ k := by exact_mod_cast hkj
    nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, sq_nonneg (Real.sin θ)]

theorem W_coord (u v : Space3) (hu : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1)
    (hv : v 0 * v 0 + v 1 * v 1 + v 2 * v 2 = 1) (huv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0)
    (t : ℝ) (i : Fin 3) : |(Real.cos t • u + Real.sin t • v) i| ≤ 1 := by
  have hs : sumsq (Real.cos t • u + Real.sin t • v) = 1 := by
    simp only [sumsq, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    linear_combination (Real.cos t) ^ 2 * hu + (Real.sin t) ^ 2 * hv
      + 2 * Real.cos t * Real.sin t * huv + Real.cos_sq_add_sin_sq t
  simp only [sumsq] at hs
  rw [← sq_le_one_iff_abs_le_one]
  fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    nlinarith [sq_nonneg ((Real.cos t • u + Real.sin t • v) 0),
      sq_nonneg ((Real.cos t • u + Real.sin t • v) 1),
      sq_nonneg ((Real.cos t • u + Real.sin t • v) 2)]

theorem trig_cases (a p q : ℝ) :
    (∀ t, 0 ≤ a + p * Real.cos t + q * Real.sin t) ∨
    (∀ t, a + p * Real.cos t + q * Real.sin t ≤ 0) ∨
    ∃ φ α : ℝ, 0 < α ∧ α < Real.pi ∧
      (∀ t, a + p * Real.cos t + q * Real.sin t = 0 →
        ∃ k : ℤ, t = φ + α + k * (2 * Real.pi) ∨ t = φ - α + k * (2 * Real.pi)) ∧
      a + p * Real.cos (φ + α) + q * Real.sin (φ + α) = 0 ∧
      a + p * Real.cos (φ - α) + q * Real.sin (φ - α) = 0 ∧
      (∀ t, φ - α ≤ t → t ≤ φ + α → 0 ≤ a + p * Real.cos t + q * Real.sin t) ∧
      (∀ t, φ + α ≤ t → t ≤ φ - α + 2 * Real.pi →
        a + p * Real.cos t + q * Real.sin t ≤ 0) := by
  set ρ := Real.sqrt (p ^ 2 + q ^ 2) with hρ
  have hbound : ∀ t, |p * Real.cos t + q * Real.sin t| ≤ ρ := by
    intro t
    apply Real.abs_le_sqrt
    nlinarith [sq_nonneg (p * Real.sin t - q * Real.cos t), Real.cos_sq_add_sin_sq t]
  by_cases h1 : ρ ≤ a
  · left; intro t; have := hbound t; rw [abs_le] at this; linarith
  by_cases h2 : ρ ≤ -a
  · right; left; intro t; have := hbound t; rw [abs_le] at this; linarith
  right; right
  have h1' : a < ρ := lt_of_not_ge h1
  have h2' : -a < ρ := lt_of_not_ge h2
  have hρpos : 0 < ρ := by linarith
  set z : ℂ := ⟨p, q⟩ with hzdef
  have hzn : ‖z‖ = ρ := by
    rw [Complex.norm_def, Complex.normSq_mk, hρ]; congr 1; ring
  have hz : z ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hzn; linarith
  set φ := Complex.arg z with hφ
  have hcφ : Real.cos φ = p / ρ := by rw [hφ, Complex.cos_arg hz, hzn]
  have hsφ : Real.sin φ = q / ρ := by rw [hφ, Complex.sin_arg, hzn]
  have hform : ∀ t, a + p * Real.cos t + q * Real.sin t = a + ρ * Real.cos (t - φ) := by
    intro t; rw [Real.cos_sub, hcφ, hsφ]; field_simp; ring
  have hm1 : -1 < -a / ρ := by rw [lt_div_iff₀ hρpos]; linarith
  have hm2 : -a / ρ < 1 := by rw [div_lt_iff₀ hρpos]; linarith
  set α := Real.arccos (-a / ρ) with hα
  have hαpos : 0 < α := Real.arccos_pos.mpr hm2
  have hαlt : α < Real.pi := Real.arccos_lt_pi.mpr hm1
  have hcα : Real.cos α = -a / ρ := Real.cos_arccos hm1.le hm2.le
  have hρcα : a + ρ * Real.cos α = 0 := by rw [hcα]; field_simp; ring
  refine ⟨φ, α, hαpos, hαlt, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    rw [hform] at ht
    have hc : Real.cos (t - φ) = Real.cos α := by
      have : ρ * Real.cos (t - φ) = ρ * Real.cos α := by linarith
      exact mul_left_cancel₀ hρpos.ne' this
    obtain ⟨k, hk⟩ := Real.cos_eq_cos_iff.mp hc
    rcases hk with hk | hk
    · exact ⟨-k, Or.inl (by push_cast; linarith)⟩
    · exact ⟨k, Or.inr (by linarith)⟩
  · rw [hform]; simp only [add_sub_cancel_left]; exact hρcα
  · rw [hform]; rw [show φ - α - φ = -α by ring, Real.cos_neg]; exact hρcα
  · intro t ht1 ht2
    rw [hform, ← Real.cos_abs]
    have hab : |t - φ| ≤ α := by rw [abs_le]; constructor <;> linarith
    have := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg (t - φ)) hαlt.le hab
    nlinarith
  · intro t ht1 ht2
    rw [hform]
    have hle : Real.cos (t - φ) ≤ Real.cos α := by
      by_cases hτ : t - φ ≤ Real.pi
      · exact Real.cos_le_cos_of_nonneg_of_le_pi hαpos.le hτ (by linarith)
      · rw [← Real.cos_two_pi_sub]
        exact Real.cos_le_cos_of_nonneg_of_le_pi hαpos.le (by linarith) (by linarith)
    nlinarith


noncomputable def Wv (u v : Space3) (t : ℝ) : Space3 := Real.cos t • u + Real.sin t • v

theorem Wv_cont (u v : Space3) : Continuous (Wv u v) := by unfold Wv; fun_prop

theorem Wv_per (u v : Space3) (t : ℝ) : Wv u v (t + 2 * Real.pi) = Wv u v t := by
  simp only [Wv, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem lift_case (n : ℕ) (c u v : Space3) (r : ℝ) (hr : 0 < r)
    (hu : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1)
    (hv : v 0 * v 0 + v 1 * v 1 + v 2 * v 2 = 1) (huv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0)
    (σ : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (hside : ∀ t, 0 ≤ σ * (c + r • Wv u v t) 2)
    (hdisj : ∀ t, c + r • Wv u v t ∉ Kset n) :
    Reach (Kset n) (Set.range fun t => c + r • Wv u v t) (standardCircle n) := by
  set h : ℝ := r + |c 2| + 2 with hh
  have hhpos : 0 < h := by positivity
  set e : Space3 := ![0, 0, σ * h] with he
  have hσ2 : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
  have step := T_range (Kset n) (K_closed n) (fun t => c + r • Wv u v t)
    (by have := Wv_cont u v; fun_prop) (fun t => by simp only [Wv_per])
    (fun _ => 1) (fun s => s • e) continuous_const (by fun_prop) (by simp) rfl (by simp)
    (by
      intro s hs t hP
      have hz := K_z hP
      simp only [Matrix.one_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul, he,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hz
      have h1 := hside t
      have h2 : σ * ((c + r • Wv u v t) 2) + s * h = 0 := by
        have : σ * ((c + r • Wv u v t) 2 + s * (σ * h)) = 0 := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]; rw [hz]; ring
        have e2 : σ * ((c + r • Wv u v t) 2 + s * (σ * h))
            = σ * ((c + r • Wv u v t) 2) + (σ * σ) * (s * h) := by ring
        rw [e2, hσ2, one_mul] at this; exact this
      have hsh : s * h = 0 := by nlinarith [mul_nonneg hs.1 hhpos.le]
      have hs0 : s = 0 := by
        rcases mul_eq_zero.1 hsh with h' | h'
        · exact h'
        · linarith
      apply hdisj t
      simpa [hs0] using hP)
    (fun t => (c + e) + r • Wv u v t) (by intro t; simp only [Matrix.one_mulVec, one_smul]; abel)
  refine reach_trans step ?_
  have := endgame n (Kset n) (K_closed n) (fun x hx => K_z hx) (fun x hx => K_not_n hx)
    (c + e) u v r hr hu hv huv ?_
  · simpa only [Wv] using this
  · simp only [Pi.add_apply, he, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    rw [lt_abs]
    rcases hσ with rfl | rfl
    · left; have := neg_abs_le (c 2); simp only [hh]; linarith
    · right; have := le_abs_self (c 2); simp only [hh]; linarith

theorem shrink_lift (n : ℕ) (c u v : Space3) (r : ℝ) (hr : 0 < r)
    (hu : u 0 * u 0 + u 1 * u 1 + u 2 * u 2 = 1)
    (hv : v 0 * v 0 + v 1 * v 1 + v 2 * v 2 = 1) (huv : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0)
    (ta : ℝ) (b' : Space3)
    (hcross : ∀ t, (c + r • Wv u v t) 2 = 0 →
      c + r • Wv u v t = c + r • Wv u v ta ∨ c + r • Wv u v t = b')
    (ha2 : (c + r • Wv u v ta) 2 = 0)
    (hseg : ∀ μ : ℝ, 0 ≤ μ → μ ≤ 1 → μ • b' + (1 - μ) • (c + r • Wv u v ta) ∉ Kset n)
    (δ : ℝ) (hδ : 0 < δ)
    (hnear : ∀ x : Space3, |x 0 - (c + r • Wv u v ta) 0| ≤ δ →
      |x 1 - (c + r • Wv u v ta) 1| ≤ δ → x ∉ Kset n) :
    Reach (Kset n) (Set.range fun t => c + r • Wv u v t) (standardCircle n) := by
  set a := c + r • Wv u v ta with ha
  set l0 : ℝ := min (1 / 2) (δ / (4 * r)) with hl0
  have hl0pos : 0 < l0 := lt_min (by norm_num) (by positivity)
  have hl0le : l0 ≤ 1 / 2 := min_le_left _ _
  have hl0δ : l0 * (2 * r) ≤ δ := by
    have := min_le_right (1 / 2 : ℝ) (δ / (4 * r))
    calc l0 * (2 * r) ≤ δ / (4 * r) * (2 * r) := by gcongr
      _ = δ / 2 := by field_simp; ring
      _ ≤ δ := by linarith
  set μ : ℝ → ℝ := fun s => 1 - s * (1 - l0) with hμ
  have hμlo : ∀ s ∈ Set.Icc (0:ℝ) 1, l0 ≤ μ s := by
    intro s hs; simp only [hμ]; nlinarith [hs.1, hs.2]
  have hμhi : ∀ s ∈ Set.Icc (0:ℝ) 1, μ s ≤ 1 := by
    intro s hs; simp only [hμ]; nlinarith [hs.1, hs.2]
  have step1 := T_range (Kset n) (K_closed n) (fun t => c + r • Wv u v t)
    (by have := Wv_cont u v; fun_prop) (fun t => by simp only [Wv_per])
    (fun s => μ s • (1 : Matrix (Fin 3) (Fin 3) ℝ)) (fun s => (1 - μ s) • a)
    (by fun_prop) (by fun_prop)
    (by
      intro s hs
      rw [Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
      exact pow_ne_zero _ (lt_of_lt_of_le hl0pos (hμlo s hs)).ne')
    (by simp [hμ]) (by simp [hμ])
    (by
      intro s hs t hP
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec] at hP
      have hz := K_z hP
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ha2, mul_zero, add_zero] at hz
      have hμpos : 0 < μ s := lt_of_lt_of_le hl0pos (hμlo s hs)
      have hft : (c + r • Wv u v t) 2 = 0 := by
        rcases mul_eq_zero.1 hz with h | h
        · linarith
        · exact h
      rcases hcross t hft with h | h
      · rw [h] at hP
        apply hseg 0 le_rfl zero_le_one
        convert hP using 1
        simp only [zero_smul, sub_zero, one_smul, zero_add]
        module
      · rw [h] at hP
        exact hseg (μ s) (hμpos.le) (hμhi s hs) hP)
    (fun t => (a + l0 • (c - a)) + (l0 * r) • Wv u v t)
    (by
      intro t
      simp only [Matrix.smul_mulVec, Matrix.one_mulVec, hμ]
      module)
  set H : ℝ := l0 * (r + |c 2|) + 2 with hH
  set e : Space3 := ![0, 0, H] with he
  have step2 := T_range (Kset n) (K_closed n) (fun t => (a + l0 • (c - a)) + (l0 * r) • Wv u v t)
    (by have := Wv_cont u v; fun_prop) (fun t => by simp only [Wv_per])
    (fun _ => 1) (fun s => s • e) continuous_const (by fun_prop) (by simp) rfl (by simp)
    (by
      intro s hs t hP
      have bound : ∀ i : Fin 3, i ≠ 2 →
          |((a + l0 • (c - a)) + (l0 * r) • Wv u v t + s • e) i - a i| ≤ δ := by
        intro i hi
        have hw1 := W_coord u v hu hv huv t i
        have hw2 := W_coord u v hu hv huv ta i
        have he_i : e i = 0 := by fin_cases i <;> simp [he] at hi ⊢
        have key : ((a + l0 • (c - a)) + (l0 * r) • Wv u v t + s • e) i - a i
            = l0 * r * ((Real.cos t • u + Real.sin t • v) i
              - (Real.cos ta • u + Real.sin ta • v) i) := by
          simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, he_i, ha, Wv]; ring
        rw [key, abs_mul, abs_of_pos (by positivity)]
        calc l0 * r * |(Real.cos t • u + Real.sin t • v) i - (Real.cos ta • u + Real.sin ta • v) i|
            ≤ l0 * r * 2 := by gcongr; exact (abs_sub _ _).trans (by linarith)
          _ = l0 * (2 * r) := by ring
          _ ≤ δ := hl0δ
      exact hnear _ (bound 0 (by decide)) (bound 1 (by decide)) (by simpa using hP))
    (fun t => (a + l0 • (c - a) + e) + (l0 * r) • Wv u v t)
    (by intro t; simp only [Matrix.one_mulVec, one_smul]; abel)
  refine reach_trans step1 (reach_trans step2 ?_)
  have := endgame n (Kset n) (K_closed n) (fun x hx => K_z hx) (fun x hx => K_not_n hx)
    (a + l0 • (c - a) + e) u v (l0 * r) (by positivity) hu hv huv ?_
  · simpa only [Wv] using this
  · have hc3 : (a + l0 • (c - a) + e) 2 = l0 * c 2 + H := by
      simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, he,
        Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
      rw [ha2]; ring
    rw [hc3, lt_abs]
    left
    have := neg_abs_le (c 2)
    simp only [hH]
    nlinarith


theorem diag_mulVec (a b : ℝ) (x : Space3) :
    Matrix.diagonal ![1, a, 1] *ᵥ x + ![0, b, 0] = ![x 0, a * x 1 + b, x 2] := by
  funext i; fin_cases i <;> simp [Matrix.mulVec_diagonal]

theorem diag_one : Matrix.diagonal (![1, 1, 1] : Fin 3 → ℝ) = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, Matrix.one_apply]

theorem diag_det (a : ℝ) : (Matrix.diagonal (![1, a, 1] : Fin 3 → ℝ)).det = a := by
  rw [Matrix.det_diagonal, Fin.prod_univ_three]; simp

theorem outside_translate (n : ℕ) (f : ℝ → Space3) (hf : Continuous f)
    (hfp : ∀ t, f (t + 2 * Real.pi) = f t)
    (qa qb : Space3) (hcross : ∀ t, f t 2 = 0 → f t = qa ∨ f t = qb)
    (hqa : ∀ j, j < n → 1 < (qa 0 - 3 * (j:ℝ)) ^ 2 + qa 1 ^ 2)
    (hqb : ∀ j, j < n → 1 < (qb 0 - 3 * (j:ℝ)) ^ 2 + qb 1 ^ 2) :
    Reach (Kset n) (Set.range f)
      (Set.range fun t => f t + ![-(max (qa 0) (qb 0) + 3), 0, 0]) := by
  set L := max (qa 0) (qb 0) + 3 with hL
  set gap : ℝ → ℝ := fun y => if y < 0 then -y else 1 with hgap
  have hgap_pos : ∀ y, 0 < gap y := by
    intro y; simp only [hgap]; split_ifs with h <;> linarith
  set ε := min (gap (qa 1)) (gap (qb 1)) / 2 with hε
  have hεpos : 0 < ε := by
    have := hgap_pos (qa 1); have := hgap_pos (qb 1)
    simp only [hε]; positivity
  have hεa : qa 1 < 0 → ε ≤ -(qa 1) / 2 := by
    intro h
    have : gap (qa 1) = -(qa 1) := by simp only [hgap, if_pos h]
    have := min_le_left (gap (qa 1)) (gap (qb 1))
    simp only [hε]; linarith
  have hεb : qb 1 < 0 → ε ≤ -(qb 1) / 2 := by
    intro h
    have : gap (qb 1) = -(qb 1) := by simp only [hgap, if_pos h]
    have := min_le_right (gap (qa 1)) (gap (qb 1))
    simp only [hε]; linarith
  -- sign facts
  have hsgn : ∀ q : Space3, (q 1 < 0 → ε ≤ -(q 1) / 2) →
      (0 ≤ q 1 → 0 < q 1 + ε) ∧ (q 1 < 0 → q 1 + ε < 0) := by
    intro q hq
    refine ⟨fun h => by linarith, fun h => by have := hq h; linarith⟩
  have hne : ∀ q : Space3, (q 1 < 0 → ε ≤ -(q 1) / 2) → q 1 + ε ≠ 0 := by
    intro q hq
    rcases le_or_gt 0 (q 1) with h | h
    · exact ((hsgn q hq).1 h).ne'
    · exact ((hsgn q hq).2 h).ne
  set m := min |qa 1 + ε| |qb 1 + ε| with hm
  have hmpos : 0 < m := lt_min (abs_pos.mpr (hne qa hεa)) (abs_pos.mpr (hne qb hεb))
  set μ1 := max 1 ((2 + ε) / m) with hμ1
  have hμ1ge : 1 ≤ μ1 := le_max_left _ _
  have hμ1pos : 0 < μ1 := by linarith
  set yc := -ε with hyc
  -- y-coordinate growth under scaling with factor μ ≥ 1
  have hgrow : ∀ q : Space3, (q 1 < 0 → ε ≤ -(q 1) / 2) → ∀ μ : ℝ, 1 ≤ μ →
      q 1 ^ 2 ≤ (μ * q 1 + (1 - μ) * yc) ^ 2 := by
    intro q hq μ hμ
    have e : μ * q 1 + (1 - μ) * yc = q 1 + (μ - 1) * (q 1 + ε) := by simp only [hyc]; ring
    rw [e]
    rcases le_or_gt 0 (q 1) with h | h
    · have := (hsgn q hq).1 h
      nlinarith [mul_nonneg (sub_nonneg.mpr hμ) this.le]
    · have := (hsgn q hq).2 h
      nlinarith [mul_nonneg (sub_nonneg.mpr hμ) (neg_nonneg.mpr this.le)]
  have hbig : ∀ q : Space3, (q 1 < 0 → ε ≤ -(q 1) / 2) → m ≤ |q 1 + ε| →
      4 ≤ (μ1 * q 1 + (1 - μ1) * yc) ^ 2 := by
    intro q hq hmq
    have e : μ1 * q 1 + (1 - μ1) * yc = μ1 * (q 1 + ε) - ε := by simp only [hyc]; ring
    rw [e]
    have h1 : (2 + ε) / m ≤ μ1 := le_max_right _ _
    have h2 : 2 + ε ≤ μ1 * |q 1 + ε| := by
      calc 2 + ε = (2 + ε) / m * m := by field_simp
        _ ≤ μ1 * |q 1 + ε| := by
          apply mul_le_mul h1 hmq hmpos.le hμ1pos.le
    have h3 : 2 ≤ |μ1 * (q 1 + ε) - ε| := by
      calc (2:ℝ) ≤ μ1 * |q 1 + ε| - ε := by linarith
        _ = |μ1 * (q 1 + ε)| - |ε| := by
            rw [abs_mul, abs_of_pos hμ1pos, abs_of_pos hεpos]
        _ ≤ |μ1 * (q 1 + ε) - ε| := abs_sub_abs_le_abs_sub _ _
    nlinarith [abs_nonneg (μ1 * (q 1 + ε) - ε), sq_abs (μ1 * (q 1 + ε) - ε)]
  -- move 1
  set μ : ℝ → ℝ := fun s => 1 + s * (μ1 - 1) with hμ
  have hμge : ∀ s ∈ Set.Icc (0:ℝ) 1, 1 ≤ μ s := by
    intro s hs; simp only [hμ]; nlinarith [hs.1]
  have step1 := T_range (Kset n) (K_closed n) f hf hfp
    (fun s => Matrix.diagonal ![1, μ s, 1]) (fun s => ![0, (1 - μ s) * yc, 0])
    (Continuous.matrix_diagonal (by fun_prop)) (by fun_prop)
    (by intro s hs; rw [diag_det]; linarith [hμge s hs])
    (by simp only [hμ, zero_mul, add_zero]; exact diag_one) (by simp [hμ])
    (by
      intro s hs t hP
      rw [diag_mulVec] at hP
      have hz := K_z hP
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hz
      obtain ⟨j, hj, hcirc⟩ := K_circle hP
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hcirc
      rcases hcross t hz with h | h
      · rw [h] at hcirc
        have := hgrow qa hεa (μ s) (hμge s hs)
        have := hqa j hj
        linarith
      · rw [h] at hcirc
        have := hgrow qb hεb (μ s) (hμge s hs)
        have := hqb j hj
        linarith)
    (fun t => ![f t 0, μ1 * f t 1 + (1 - μ1) * yc, f t 2])
    (by intro t; rw [diag_mulVec]; simp only [hμ, one_mul, add_sub_cancel])
  -- move 2
  have step2 := T_range (Kset n) (K_closed n) (fun t => ![f t 0, μ1 * f t 1 + (1 - μ1) * yc, f t 2])
    (by fun_prop) (fun t => by simp only [hfp])
    (fun _ => 1) (fun s => s • ![-L, 0, 0]) continuous_const (by fun_prop) (by simp) rfl (by simp)
    (by
      intro s hs t hP
      simp only [Matrix.one_mulVec] at hP
      have hz := K_z hP
      simp at hz
      have hx1 := K_x1 hP
      simp at hx1
      rcases hcross t hz with h | h
      · rw [h] at hx1
        have := hbig qa hεa (min_le_left _ _)
        nlinarith [sq_abs (μ1 * qa 1 + (1 - μ1) * yc), abs_nonneg (μ1 * qa 1 + (1 - μ1) * yc)]
      · rw [h] at hx1
        have := hbig qb hεb (min_le_right _ _)
        nlinarith [sq_abs (μ1 * qb 1 + (1 - μ1) * yc), abs_nonneg (μ1 * qb 1 + (1 - μ1) * yc)])
    (fun t => ![f t 0 - L, μ1 * f t 1 + (1 - μ1) * yc, f t 2])
    (by intro t; funext i; fin_cases i <;> simp; ring)
  -- move 3
  set ν : ℝ → ℝ := fun s => 1 + s * (μ1⁻¹ - 1) with hν
  have hνpos : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 < ν s := by
    intro s hs
    have hi : 0 < μ1⁻¹ := inv_pos.mpr hμ1pos
    simp only [hν]
    rcases hs.2.lt_or_eq with h | h
    · nlinarith [mul_nonneg hs.1 hi.le]
    · rw [h]; linarith
  have step3 := T_range (Kset n) (K_closed n)
    (fun t => ![f t 0 - L, μ1 * f t 1 + (1 - μ1) * yc, f t 2])
    (by fun_prop) (fun t => by simp only [hfp])
    (fun s => Matrix.diagonal ![1, ν s, 1]) (fun s => ![0, (1 - ν s) * yc, 0])
    (Continuous.matrix_diagonal (by fun_prop)) (by fun_prop)
    (by intro s hs; rw [diag_det]; exact (hνpos s hs).ne')
    (by simp only [hν, zero_mul, add_zero]; exact diag_one) (by simp [hν])
    (by
      intro s hs t hP
      rw [diag_mulVec] at hP
      have hz := K_z hP
      simp only [Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at hz
      have hx0 := K_x0 hP
      simp only [Matrix.cons_val_zero] at hx0
      rcases hcross t hz with h | h
      · rw [h] at hx0
        have := le_max_left (qa 0) (qb 0)
        simp only [hL] at hx0; linarith
      · rw [h] at hx0
        have := le_max_right (qa 0) (qb 0)
        simp only [hL] at hx0; linarith)
    (fun t => f t + ![-L, 0, 0])
    (by
      intro t
      rw [diag_mulVec]
      funext i; fin_cases i <;> simp [hν]
      · ring
      · field_simp; ring)
  exact reach_trans step1 (reach_trans step2 step3)

end F494

/- Source module: EllipseBarrier -/

/-! The new geometric invariant needed for simultaneous circle shrinking.
The covering-space and crossing lemmas used here are from Nickrobbins95's
accepted submission, preserved in `ReferenceTools`. -/

noncomputable section
namespace BookCircleCompletion
open BookSixth F494

/-- An unlinked component gives a periodic logarithm for any continuous
complex-valued function whose zero set is contained in the other component. -/
theorem unlink_periodic_log (C : Set Space3) (d : ℝ → Space3)
    (hd : Continuous d) (hdper : ∀ t, d (t + 2 * Real.pi) = d t)
    (hU : IsUnlink (![Set.range d, C] : Fin 2 → Set Space3))
    (F : Space3 → ℂ) (hF : Continuous F) (hzero : ∀ x, F x = 0 → x ∈ C) :
    ∃ Λ : ℝ → ℂ, Continuous Λ ∧ (∀ t, Complex.exp (Λ t) = F (d t)) ∧
      ∀ t, Λ (t + 2 * Real.pi) = Λ t := by
  obtain ⟨H, _, _, _, h1⟩ := hU
  have hD : H 1 '' Set.range d = standardCircle 0 := by simpa using h1 0
  have hC : H 1 '' C = standardCircle 1 := by simpa using h1 1
  have hmemD : ∀ t, H 1 (d t) ∈ standardCircle 0 :=
    fun t => hD ▸ ⟨d t, ⟨t, rfl⟩, rfl⟩
  have hmemC : ∀ x ∈ C, H 1 x ∈ standardCircle 1 :=
    fun x hx => hC ▸ ⟨x, hx, rfl⟩
  let κ : ℝ → ℝ := fun s => max 0 (min s 1)
  have hκc : Continuous κ := by fun_prop
  have hκ0 : ∀ s, 0 ≤ κ s := fun s => le_max_left _ _
  have hκ1 : ∀ s, κ s ≤ 1 := fun s => max_le zero_le_one (min_le_right _ _)
  let Φ : ℝ × ℝ → Space3 := fun p => (H 1).symm ((1 - κ p.1) • H 1 (d p.2))
  have hΦc : Continuous Φ := by
    exact (H 1).symm.continuous.comp
      ((continuous_const.sub (hκc.comp continuous_fst)).smul
        ((H 1).continuous.comp (hd.comp continuous_snd)))
  have hΦC : ∀ p, Φ p ∉ C := by
    intro p hp
    have hm := hmemC _ hp
    simp only [Φ, Homeomorph.apply_symm_apply] at hm
    have h2 := std_x0_ge _ hm
    have h3 := std_x0_le _ (hmemD p.2)
    simp only [Pi.smul_apply, smul_eq_mul] at h2
    have := hκ0 p.1
    have := hκ1 p.1
    nlinarith
  obtain ⟨Λ, hΛc, hΛe, hΛp⟩ := periodic_log (fun p => F (Φ p)) (hF.comp hΦc)
    (fun p h => hΦC p (hzero _ h))
    (fun s t => by simp only [Φ, hdper])
    (fun t => by simp [Φ, κ])
  refine ⟨Λ, hΛc, fun t => ?_, hΛp⟩
  rw [hΛe]
  simp [Φ, κ]

def ellipse (a b c d e f t : ℝ) : ℂ :=
  ⟨a + b * Real.cos t + c * Real.sin t,
    d + e * Real.cos t + f * Real.sin t⟩

theorem ellipse_continuous (a b c d e f : ℝ) :
    Continuous (ellipse a b c d e f) := by
  have he : ellipse a b c d e f = fun t =>
      ((a + b * Real.cos t + c * Real.sin t : ℝ) : ℂ) +
      ((d + e * Real.cos t + f * Real.sin t : ℝ) : ℂ) * Complex.I := by
    funext t
    apply Complex.ext <;>
      simp only [ellipse, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im] <;> ring
  rw [he]
  fun_prop

/-- A periodic logarithm rules out a zero strictly inside an affine ellipse.
This version assumes its imaginary part is nonconstant. -/
theorem ellipse_interior_no_zero_of_im (a b c d e f : ℝ)
    (hef : 0 < e ^ 2 + f ^ 2)
    (Λ : ℝ → ℂ) (hΛ : Continuous Λ)
    (hexp : ∀ t, Complex.exp (Λ t) = ellipse a b c d e f t)
    (hper : ∀ t, Λ (t + 2 * Real.pi) = Λ t)
    (x y : ℝ) (hxy : x ^ 2 + y ^ 2 < 1)
    (hre : a + b * x + c * y = 0) (him : d + e * x + f * y = 0) : False := by
  let R := Real.sqrt (e ^ 2 + f ^ 2)
  have hR : 0 < R := Real.sqrt_pos.2 hef
  have hRsq : R ^ 2 = e ^ 2 + f ^ 2 := Real.sq_sqrt hef.le
  obtain ⟨φ, hcφ, hsφ⟩ := exists_angle (e / R) (f / R) (by
    field_simp
    nlinarith [hRsq])
  have he : e = R * Real.cos φ := by rw [hcφ]; field_simp
  have hf : f = R * Real.sin φ := by rw [hsφ]; field_simp
  let z := Real.cos φ * x + Real.sin φ * y
  let q := -Real.sin φ * x + Real.cos φ * y
  have hzq : z ^ 2 + q ^ 2 = x ^ 2 + y ^ 2 := by
    dsimp [z, q]
    linear_combination (x ^ 2 + y ^ 2) * Real.cos_sq_add_sin_sq φ
  have hzlt : -1 < z ∧ z < 1 := by constructor <;> nlinarith [sq_nonneg q]
  let α := Real.arccos z
  have hαpos : 0 < α := Real.arccos_pos.2 hzlt.2
  have hαlt : α < Real.pi := Real.arccos_lt_pi.2 hzlt.1
  have hcα : Real.cos α = z := Real.cos_arccos hzlt.1.le hzlt.2.le
  have hd : d = -R * z := by
    dsimp [z]
    rw [he, hf] at him
    nlinarith only [him]
  have himform : ∀ t, (ellipse a b c d e f t).im = R * (Real.cos (t - φ) - z) := by
    intro t
    simp only [ellipse, Real.cos_sub]
    rw [he, hf, hd]
    ring
  let P := b * Real.cos φ + c * Real.sin φ
  let Q := -b * Real.sin φ + c * Real.cos φ
  have ha : a = -P * z - Q * q := by
    dsimp [P, Q, z, q]
    linear_combination hre + (b * x + c * y) * Real.cos_sq_add_sin_sq φ
  have hreform : ∀ t, (ellipse a b c d e f t).re =
      a + P * Real.cos (t - φ) + Q * Real.sin (t - φ) := by
    intro t
    dsimp [ellipse, P, Q]
    rw [Real.cos_sub, Real.sin_sub]
    linear_combination -(b * Real.cos t + c * Real.sin t) * Real.cos_sq_add_sin_sq φ
  have haim : (ellipse a b c d e f (φ - α)).im = 0 := by
    rw [himform, show φ - α - φ = -α by ring, Real.cos_neg, hcα]
    ring
  have hbim : (ellipse a b c d e f (φ + α)).im = 0 := by
    rw [himform, show φ + α - φ = α by ring, hcα]
    ring
  have hare : (ellipse a b c d e f (φ - α)).re = -Q * (q + Real.sin α) := by
    rw [hreform, show φ - α - φ = -α by ring, Real.cos_neg, Real.sin_neg, hcα, ha]
    ring
  have hbre : (ellipse a b c d e f (φ + α)).re = Q * (Real.sin α - q) := by
    rw [hreform, show φ + α - φ = α by ring, hcα, ha]
    ring
  have hQ : Q ≠ 0 := by
    intro h
    have hn := Complex.exp_ne_zero (Λ (φ - α))
    rw [hexp] at hn
    apply hn
    apply Complex.ext
    · simpa [h] using hare
    · exact haim
  have hsign : (ellipse a b c d e f (φ - α)).re *
      (ellipse a b c d e f (φ + α)).re < 0 := by
    rw [hare, hbre]
    have ht := Real.cos_sq_add_sin_sq α
    rw [hcα] at ht
    have hneg : q ^ 2 - Real.sin α ^ 2 < 0 := by nlinarith
    have hp := mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hQ) hneg
    nlinarith only [hp]
  apply crossing_false (ellipse a b c d e f) Λ (ellipse_continuous ..) hΛ hexp hper
    (φ - α) (φ + α) (by linarith) (by linarith) ?_ ?_ haim hbim hsign
  · intro t ht1 ht2
    rw [himform]
    apply mul_nonneg hR.le
    rw [sub_nonneg, ← hcα, ← Real.cos_abs (t - φ)]
    apply Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) hαlt.le
    rw [abs_le]
    constructor <;> linarith
  · intro t ht1 ht2
    rw [himform]
    apply mul_nonpos_of_nonneg_of_nonpos hR.le
    rw [sub_nonpos, ← hcα]
    by_cases ht : t - φ ≤ Real.pi
    · exact Real.cos_le_cos_of_nonneg_of_le_pi hαpos.le ht (by linarith)
    · rw [← Real.cos_two_pi_sub]
      exact Real.cos_le_cos_of_nonneg_of_le_pi hαpos.le (by linarith) (by linarith)

theorem ellipse_interior_no_zero (a b c d e f : ℝ)
    (Λ : ℝ → ℂ) (hΛ : Continuous Λ)
    (hexp : ∀ t, Complex.exp (Λ t) = ellipse a b c d e f t)
    (hper : ∀ t, Λ (t + 2 * Real.pi) = Λ t)
    (x y : ℝ) (hxy : x ^ 2 + y ^ 2 < 1)
    (hre : a + b * x + c * y = 0) (him : d + e * x + f * y = 0) : False := by
  by_cases hef : 0 < e ^ 2 + f ^ 2
  · exact ellipse_interior_no_zero_of_im a b c d e f hef Λ hΛ hexp hper x y hxy hre him
  have he : e = 0 := by nlinarith [sq_nonneg f, sq_nonneg e]
  have hf : f = 0 := by nlinarith [sq_nonneg f, sq_nonneg e]
  by_cases hbc : 0 < b ^ 2 + c ^ 2
  · apply ellipse_interior_no_zero_of_im (-d) (-e) (-f) a b c hbc
      (fun t => Λ t + (Real.pi / 2 * Complex.I)) (by fun_prop) ?_
      (fun t => by simp only [hper]) x y hxy (by linarith) hre
    intro t
    rw [Complex.exp_add, Complex.exp_pi_div_two_mul_I, hexp]
    apply Complex.ext <;> simp [ellipse, Complex.mul_re, Complex.mul_im] <;> ring
  have hb : b = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
  have hc : c = 0 := by nlinarith [sq_nonneg b, sq_nonneg c]
  have ha : a = 0 := by simpa [hb, hc] using hre
  have hd : d = 0 := by simpa [he, hf] using him
  have hn := Complex.exp_ne_zero (Λ 0)
  rw [hexp] at hn
  apply hn
  apply Complex.ext <;> simp [ellipse, ha, hb, hc, hd, he, hf]

/-- The closed filled ellipse misses zero, including its boundary. -/
theorem ellipse_disk_no_zero (a b c d e f : ℝ)
    (Λ : ℝ → ℂ) (hΛ : Continuous Λ)
    (hexp : ∀ t, Complex.exp (Λ t) = ellipse a b c d e f t)
    (hper : ∀ t, Λ (t + 2 * Real.pi) = Λ t)
    (x y : ℝ) (hxy : x ^ 2 + y ^ 2 ≤ 1)
    (hre : a + b * x + c * y = 0) (him : d + e * x + f * y = 0) : False := by
  rcases hxy.lt_or_eq with hlt | heq
  · exact ellipse_interior_no_zero a b c d e f Λ hΛ hexp hper x y hlt hre him
  obtain ⟨t, ht1, ht2⟩ := exists_angle x y heq
  have hn := Complex.exp_ne_zero (Λ t)
  rw [hexp] at hn
  apply hn
  apply Complex.ext <;> simp [ellipse, ht1, ht2, hre, him]

end BookCircleCompletion

/- Source module: CircleGeometry -/

noncomputable section
namespace BookCircleCompletion
open BookSixth Matrix F494

/-- Explicit Euclidean data; `Space3` itself has the sup norm. -/
structure CircleData where
  c : Space3
  u : Space3
  v : Space3
  r : ℝ
  hr : 0 < r
  hu : u ⬝ᵥ u = 1
  hv : v ⬝ᵥ v = 1
  huv : u ⬝ᵥ v = 0

def CircleData.normal (D : CircleData) : Space3 := D.u ⨯₃ D.v

def CircleData.point (D : CircleData) (s t : ℝ) : Space3 :=
  D.c + s • (Real.cos t • D.u + Real.sin t • D.v)

def CircleData.curve (D : CircleData) (s : ℝ) : Set Space3 := Set.range (D.point s)

theorem CircleData.point_continuous (D : CircleData) (s : ℝ) :
    Continuous (D.point s) := by unfold CircleData.point; fun_prop

theorem CircleData.point_periodic (D : CircleData) (s t : ℝ) :
    D.point s (t + 2 * Real.pi) = D.point s t := by
  simp [CircleData.point, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem CircleData.normal_u (D : CircleData) : D.normal ⬝ᵥ D.u = 0 := by
  rw [dotProduct_comm]
  exact dot_self_cross _ _

theorem CircleData.normal_v (D : CircleData) : D.normal ⬝ᵥ D.v = 0 := by
  rw [dotProduct_comm]
  exact dot_cross_self _ _

theorem CircleData.normal_unit (D : CircleData) : D.normal ⬝ᵥ D.normal = 1 := by
  simp only [CircleData.normal, cross_dot_cross, D.hu, D.hv, D.huv,
    show D.v ⬝ᵥ D.u = 0 by rw [dotProduct_comm]; exact D.huv]
  norm_num

theorem CircleData.frame_decomposition (D : CircleData) (x : Space3) :
    (D.u ⬝ᵥ x) • D.u + (D.v ⬝ᵥ x) • D.v + (D.normal ⬝ᵥ x) • D.normal = x := by
  have hu := D.hu
  have hv := D.hv
  have huv := D.huv
  simp only [dotProduct, Fin.sum_univ_three] at hu hv huv
  ext i
  fin_cases i <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, CircleData.normal,
      cross_apply, dotProduct, Fin.sum_univ_three, cons_val_zero, cons_val_one,
      cons_val_two, head_cons, tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk] <;>
    (first
    | linear_combination
        ((D.v 0 * D.v 0 + D.v 1 * D.v 1 + D.v 2 * D.v 2) * x 0 -
          (D.v 0 * x 0 + D.v 1 * x 1 + D.v 2 * x 2) * D.v 0) * hu +
        (x 0 - (D.u 0 * x 0 + D.u 1 * x 1 + D.u 2 * x 2) * D.u 0) * hv +
        ((D.v 0 * x 0 + D.v 1 * x 1 + D.v 2 * x 2) * D.u 0 +
          (D.u 0 * x 0 + D.u 1 * x 1 + D.u 2 * x 2) * D.v 0 -
          (D.u 0 * D.v 0 + D.u 1 * D.v 1 + D.u 2 * D.v 2) * x 0) * huv
    | linear_combination
        ((D.v 0 * D.v 0 + D.v 1 * D.v 1 + D.v 2 * D.v 2) * x 1 -
          (D.v 0 * x 0 + D.v 1 * x 1 + D.v 2 * x 2) * D.v 1) * hu +
        (x 1 - (D.u 0 * x 0 + D.u 1 * x 1 + D.u 2 * x 2) * D.u 1) * hv +
        ((D.v 0 * x 0 + D.v 1 * x 1 + D.v 2 * x 2) * D.u 1 +
          (D.u 0 * x 0 + D.u 1 * x 1 + D.u 2 * x 2) * D.v 1 -
          (D.u 0 * D.v 0 + D.u 1 * D.v 1 + D.u 2 * D.v 2) * x 1) * huv
    | linear_combination
        ((D.v 0 * D.v 0 + D.v 1 * D.v 1 + D.v 2 * D.v 2) * x 2 -
          (D.v 0 * x 0 + D.v 1 * x 1 + D.v 2 * x 2) * D.v 2) * hu +
        (x 2 - (D.u 0 * x 0 + D.u 1 * x 1 + D.u 2 * x 2) * D.u 2) * hv +
        ((D.v 0 * x 0 + D.v 1 * x 1 + D.v 2 * x 2) * D.u 2 +
          (D.u 0 * x 0 + D.u 1 * x 1 + D.u 2 * x 2) * D.v 2 -
          (D.u 0 * D.v 0 + D.u 1 * D.v 1 + D.u 2 * D.v 2) * x 2) * huv)

theorem CircleData.pythagoras (D : CircleData) (x : Space3) :
    (D.u ⬝ᵥ x) ^ 2 + (D.v ⬝ᵥ x) ^ 2 + (D.normal ⬝ᵥ x) ^ 2 = x ⬝ᵥ x := by
  calc
    _ = ((D.u ⬝ᵥ x) • D.u + (D.v ⬝ᵥ x) • D.v +
      (D.normal ⬝ᵥ x) • D.normal) ⬝ᵥ x := by
        simp only [add_dotProduct, smul_dotProduct, smul_eq_mul]
        ring
    _ = _ := by rw [D.frame_decomposition]

def CircleData.linkMap (D : CircleData) (x : Space3) : ℂ :=
  ⟨(x - D.c) ⬝ᵥ (x - D.c) - D.r ^ 2, D.normal ⬝ᵥ (x - D.c)⟩

theorem CircleData.linkMap_zero (D : CircleData) (x : Space3)
    (h : D.linkMap x = 0) : x ∈ D.curve D.r := by
  have hre : (x - D.c) ⬝ᵥ (x - D.c) = D.r ^ 2 := by
    have := congrArg Complex.re h
    simpa [CircleData.linkMap, sub_eq_zero] using this
  have him : D.normal ⬝ᵥ (x - D.c) = 0 := by
    exact congrArg Complex.im h
  have hp := D.pythagoras (x - D.c)
  rw [him, hre] at hp
  obtain ⟨t, hc, hs⟩ := exists_angle ((D.u ⬝ᵥ (x - D.c)) / D.r)
      ((D.v ⬝ᵥ (x - D.c)) / D.r) (by
    field_simp [D.hr.ne']
    nlinarith only [hp])
  refine ⟨t, ?_⟩
  have hframe := D.frame_decomposition (x - D.c)
  rw [him, zero_smul, add_zero] at hframe
  simp only [CircleData.point, hc, hs, smul_add, smul_smul]
  rw [mul_div_cancel₀ _ D.hr.ne', mul_div_cancel₀ _ D.hr.ne']
  rw [hframe]
  abel

theorem CircleData.linkMap_continuous (D : CircleData) : Continuous D.linkMap := by
  have he : D.linkMap = fun x =>
      (((x - D.c) ⬝ᵥ (x - D.c) - D.r ^ 2 : ℝ) : ℂ) +
      ((D.normal ⬝ᵥ (x - D.c) : ℝ) : ℂ) * Complex.I := by
    funext x
    apply Complex.ext <;>
      simp only [CircleData.linkMap, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im] <;> ring
  rw [he]
  simp only [dotProduct]
  fun_prop

theorem CircleData.direction_unit (D : CircleData) (t : ℝ) :
    (Real.cos t • D.u + Real.sin t • D.v) ⬝ᵥ
      (Real.cos t • D.u + Real.sin t • D.v) = 1 := by
  have hvu : D.v ⬝ᵥ D.u = 0 := by rw [dotProduct_comm]; exact D.huv
  simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, D.hu, D.hv, D.huv, hvu]
  nlinarith [Real.cos_sq_add_sin_sq t]

theorem CircleData.point_power (D : CircleData) (s t : ℝ) :
    (D.point s t - D.c) ⬝ᵥ (D.point s t - D.c) = s ^ 2 := by
  simp only [CircleData.point, add_sub_cancel_left, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, D.direction_unit]
  ring

theorem CircleData.point_plane (D : CircleData) (s t : ℝ) :
    D.normal ⬝ᵥ (D.point s t - D.c) = 0 := by
  simp [CircleData.point, dotProduct_add, D.normal_u, D.normal_v]

theorem CircleData.linkMap_point (D E : CircleData) (s t : ℝ) :
    E.linkMap (D.point s t) = ellipse
      ((D.c - E.c) ⬝ᵥ (D.c - E.c) + s ^ 2 - E.r ^ 2)
      (2 * s * ((D.c - E.c) ⬝ᵥ D.u))
      (2 * s * ((D.c - E.c) ⬝ᵥ D.v))
      (E.normal ⬝ᵥ (D.c - E.c))
      (s * (E.normal ⬝ᵥ D.u)) (s * (E.normal ⬝ᵥ D.v)) t := by
  have he : D.point s t - E.c = D.c - E.c + s •
      (Real.cos t • D.u + Real.sin t • D.v) := by
    simp only [CircleData.point]
    abel
  have hvu : D.v ⬝ᵥ D.u = 0 := by rw [dotProduct_comm]; exact D.huv
  apply Complex.ext
  · simp only [CircleData.linkMap, ellipse, he, add_dotProduct, dotProduct_add,
      smul_dotProduct, dotProduct_smul, smul_eq_mul, D.hu, D.hv, D.huv, hvu,
      show D.u ⬝ᵥ (D.c - E.c) = (D.c - E.c) ⬝ᵥ D.u from dotProduct_comm _ _,
      show D.v ⬝ᵥ (D.c - E.c) = (D.c - E.c) ⬝ᵥ D.v from dotProduct_comm _ _]
    linear_combination s ^ 2 * Real.cos_sq_add_sin_sq t
  · simp only [CircleData.linkMap, ellipse, he, dotProduct_add, dotProduct_smul, smul_eq_mul]
    ring

/-- Subtracting the same nonnegative number from the squared radii preserves
disjointness, even at a zero-radius endpoint. This is the hemisphere lemma. -/
theorem canonical_shrink_disjoint (D E : CircleData)
    (hU : IsUnlink (![D.curve D.r, E.curve E.r] : Fin 2 → Set Space3))
    (h s t : ℝ) (hh : 0 ≤ h)
    (hs : s ^ 2 = D.r ^ 2 - h) (ht : t ^ 2 = E.r ^ 2 - h) :
    Disjoint (D.curve s) (E.curve t) := by
  obtain ⟨Λ, hΛ, hΛe, hΛp⟩ := unlink_periodic_log (E.curve E.r) (D.point D.r)
    (D.point_continuous _) (D.point_periodic _) hU E.linkMap
    E.linkMap_continuous E.linkMap_zero
  rw [Set.disjoint_left]
  rintro x ⟨θ, hθ⟩ ⟨φ, hφ⟩
  have hpoint : D.point s θ = E.point t φ := hθ.trans hφ.symm
  have hzeroim : (E.linkMap (D.point s θ)).im = 0 := by
    rw [hpoint]
    exact E.point_plane t φ
  have hzerore : (E.linkMap (D.point s θ)).re = -h := by
    rw [hpoint]
    change (E.point t φ - E.c) ⬝ᵥ (E.point t φ - E.c) - E.r ^ 2 = -h
    rw [E.point_power, ht]
    ring
  have hxy : (s / D.r * Real.cos θ) ^ 2 + (s / D.r * Real.sin θ) ^ 2 ≤ 1 := by
    have heq : (s / D.r * Real.cos θ) ^ 2 + (s / D.r * Real.sin θ) ^ 2 =
        s ^ 2 / D.r ^ 2 := by
      field_simp [D.hr.ne']
      linear_combination s ^ 2 * Real.cos_sq_add_sin_sq θ
    rw [heq]
    apply (div_le_one (sq_pos_of_pos D.hr)).2
    linarith
  apply ellipse_disk_no_zero
    ((D.c - E.c) ⬝ᵥ (D.c - E.c) + D.r ^ 2 - E.r ^ 2)
    (2 * D.r * ((D.c - E.c) ⬝ᵥ D.u))
    (2 * D.r * ((D.c - E.c) ⬝ᵥ D.v))
    (E.normal ⬝ᵥ (D.c - E.c))
    (D.r * (E.normal ⬝ᵥ D.u)) (D.r * (E.normal ⬝ᵥ D.v))
    Λ hΛ (fun θ => by rw [hΛe, D.linkMap_point]) hΛp
    (s / D.r * Real.cos θ) (s / D.r * Real.sin θ) hxy
  · rw [D.linkMap_point] at hzerore
    change _ + _ * Real.cos θ + _ * Real.sin θ = -h at hzerore
    field_simp [D.hr.ne']
    linear_combination hzerore - hs
  · rw [D.linkMap_point] at hzeroim
    change _ + _ * Real.cos θ + _ * Real.sin θ = 0 at hzeroim
    field_simp [D.hr.ne']
    linear_combination hzeroim

theorem circleData_of_round {C : Set Space3} (hC : RoundCircle C) :
    ∃ D : CircleData, D.curve D.r = C := by
  obtain ⟨c, u, v, r, hr, hu, hv, huv, hC⟩ := hC
  let D : CircleData := ⟨c, u, v, r, hr, hu, hv, huv⟩
  refine ⟨D, ?_⟩
  rw [hC]
  apply congrArg Set.range
  funext t
  dsimp [CircleData.point, D]
  module

end BookCircleCompletion

/- Source module: FamilyMotion -/

noncomputable section
namespace BookCircleCompletion
open BookSixth F494 Matrix Set Filter
open scoped Topology

def FamilyMotion {ι : Type*} (C D : ι → Set Space3) : Prop :=
  ∃ H : ℝ → Space3 ≃ₜ Space3,
    Continuous (fun p : ℝ × Space3 => H p.1 p.2) ∧
    Continuous (fun p : ℝ × Space3 => (H p.1).symm p.2) ∧
    (∀ x, H 0 x = x) ∧ ∀ i, (H 1) '' C i = D i

theorem FamilyMotion.refl {ι : Type*} (C : ι → Set Space3) : FamilyMotion C C :=
  ⟨fun _ => Homeomorph.refl _, continuous_snd, continuous_snd, fun _ => rfl,
    fun _ => by simp⟩

theorem FamilyMotion.trans {ι : Type*} {C D E : ι → Set Space3}
    (h1 : FamilyMotion C D) (h2 : FamilyMotion D E) : FamilyMotion C E := by
  obtain ⟨H, hH, hHi, hH0, hH1⟩ := h1
  obtain ⟨G, hG, hGi, hG0, hG1⟩ := h2
  refine ⟨fun t => (H t).trans (G t), hG.comp (continuous_fst.prodMk hH),
    hHi.comp (continuous_fst.prodMk hGi), ?_, ?_⟩
  · intro x; simp [hH0, hG0]
  · intro i
    rw [← hG1 i, ← hH1 i, ← Set.image_comp]
    rfl

theorem FamilyMotion.symm {ι : Type*} {C D : ι → Set Space3}
    (h : FamilyMotion C D) : FamilyMotion D C := by
  obtain ⟨H, hH, hHi, hH0, hH1⟩ := h
  refine ⟨fun t => (H t).symm, hHi, hH, ?_, ?_⟩
  · intro x
    apply (H 0).injective
    rw [Homeomorph.apply_symm_apply, hH0]
  · intro i
    rw [← hH1 i, ← Set.image_comp]
    simp

theorem FamilyMotion.isUnlink {m : ℕ} {C D : Fin m → Set Space3}
    (h : FamilyMotion C D) (hD : IsUnlink D) : IsUnlink C :=
  h.trans hD

theorem FamilyMotion.reindex {ι κ : Type*} {C D : ι → Set Space3}
    (h : FamilyMotion C D) (f : κ → ι) : FamilyMotion (C ∘ f) (D ∘ f) := by
  obtain ⟨H, hc, hi, h0, h1⟩ := h
  exact ⟨H, hc, hi, h0, fun j => h1 (f j)⟩

theorem FamilyMotion.pair {ι : Type*} {C D : ι → Set Space3}
    (h : FamilyMotion C D) (i j : ι) :
    FamilyMotion (![C i, C j] : Fin 2 → Set Space3) (![D i, D j] : Fin 2 → Set Space3) := by
  obtain ⟨H, hc, hi, h0, h1⟩ := h
  refine ⟨H, hc, hi, h0, fun k => ?_⟩
  fin_cases k
  · simpa using h1 i
  · simpa using h1 j

theorem FamilyMotion.disjoint {ι : Type*} {C D : ι → Set Space3}
    (h : FamilyMotion C D) (i j : ι) (hd : Disjoint (C i) (C j)) :
    Disjoint (D i) (D j) := by
  obtain ⟨H, _, _, _, h1⟩ := h
  rw [← h1 i, ← h1 j, Set.disjoint_left]
  rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, he⟩
  have heq : y = x := (H 1).injective he
  exact Set.disjoint_left.1 hd hx (heq ▸ hy)

/-- Moving each component while fixing all the other old and new components
is sufficient to move the labelled family. -/
theorem family_motion_of_component_moves {ι : Type*} [Fintype ι]
    (C D : ι → Set Space3)
    (hm : ∀ i, Reach {x | ∃ j, j ≠ i ∧ (x ∈ C j ∨ x ∈ D j)} (C i) (D i)) :
    FamilyMotion C D := by
  classical
  have hfin : ∀ s : Finset ι, FamilyMotion C (fun i => if i ∈ s then D i else C i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using FamilyMotion.refl C
    | @insert j s hj ih =>
      obtain ⟨G, hG, hGi, hG0, hfix, hG1⟩ := hm j
      apply ih.trans
      refine ⟨G, hG, hGi, hG0, fun i => ?_⟩
      by_cases hij : i = j
      · subst i
        simpa [hj] using hG1
      · have heq : ∀ x ∈ (if i ∈ s then D i else C i), G 1 x = x := by
          intro x hx
          apply hfix 1 x
          refine ⟨i, hij, ?_⟩
          by_cases hi : i ∈ s
          · exact Or.inr (by simpa [hi] using hx)
          · exact Or.inl (by simpa [hi] using hx)
        have hset : G 1 '' (if i ∈ s then D i else C i) =
            (if i ∈ s then D i else C i) := by
          convert Set.image_id (if i ∈ s then D i else C i) using 1
          exact Set.image_congr heq
        simpa [Finset.mem_insert, hij] using hset
  simpa using hfin Finset.univ

theorem finite_positive_lower_bound {ι : Type*} [Fintype ι] (f : ι → ℝ)
    (hf : ∀ i, 0 < f i) : ∃ ε > 0, ∀ i, ε ≤ f i := by
  classical
  have hfin : ∀ s : Finset ι, ∃ ε > 0, ∀ i ∈ s, ε ≤ f i := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, one_pos, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨ε, hε, he⟩ := ih
      refine ⟨min ε (f i), lt_min hε (hf i), fun j hj => ?_⟩
      rcases Finset.mem_insert.1 hj with rfl | hj
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (he j hj)
  simpa using hfin Finset.univ

theorem compact_family_separation {ι : Type*} [Fintype ι]
    (C : ι → Set Space3) (hc : ∀ i, IsCompact (C i)) (hne : ∀ i, (C i).Nonempty)
    (hd : ∀ i j, i ≠ j → Disjoint (C i) (C j)) :
    ∃ ρ > 0, ∀ i j, i ≠ j → ∀ x ∈ C i, 2 * ρ ≤ Metric.infDist x (C j) := by
  have hpair : ∀ p : ι × ι, ∃ ε > 0,
      ∀ x ∈ C p.1, p.1 ≠ p.2 → ε ≤ Metric.infDist x (C p.2) := by
    intro p
    by_cases hp : p.1 = p.2
    · exact ⟨1, one_pos, fun _ _ h => (h hp).elim⟩
    obtain ⟨x, hx, hmin⟩ := (hc p.1).exists_isMinOn (hne p.1)
      (Metric.continuous_infDist_pt (s := C p.2)).continuousOn
    have hn : x ∉ C p.2 := fun hx2 => Set.disjoint_left.1 (hd _ _ hp) hx hx2
    exact ⟨Metric.infDist x (C p.2), ((hc p.2).isClosed.notMem_iff_infDist_pos (hne _)).1 hn,
      fun y hy _ => hmin hy⟩
  choose ε hε he using hpair
  obtain ⟨δ, hδ, hdε⟩ := finite_positive_lower_bound ε hε
  refine ⟨δ / 2, half_pos hδ, fun i j hij x hx => ?_⟩
  calc 2 * (δ / 2) = δ := by ring
    _ ≤ ε (i, j) := hdε _
    _ ≤ Metric.infDist x (C j) := he (i, j) x hx hij

/-- Small affine changes to finitely many separated components extend to
an ambient motion. The estimates are in the actual sup norm of Space3. -/
theorem simultaneous_small_step {ι : Type*} [Fintype ι]
    (C : ι → Set Space3) (hne : ∀ i, (C i).Nonempty)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hsep : ∀ i j, i ≠ j → ∀ x ∈ C i, 2 * ρ ≤ Metric.infDist x (C j))
    (B : ι → Space3 → Space3) (hB : ∀ i, Continuous (B i))
    (hBlip : ∀ i x y, ‖(B i x - x) - (B i y - y)‖ ≤ 1 / 4 * ‖x - y‖)
    (hsmall : ∀ i y, Metric.infDist y (C i) < ρ → ‖B i y - y‖ ≤ ρ / 4) :
    FamilyMotion C (fun i => B i '' C i) := by
  apply family_motion_of_component_moves
  intro i
  apply step_reach _ (C i) (C i) ρ hρ (hne i) ?_ (fun _ h => h) (B i)
    (hB i) (hBlip i) (hsmall i)
  rintro k ⟨j, hji, hk | ⟨x, hx, rfl⟩⟩
  · have := hsep j i hji k hk
    linarith
  · have h1 := hsep j i hji x hx
    have h2 := Metric.infDist_le_infDist_add_dist (x := x) (y := B j x) (s := C i)
    have h3 := hsmall j x (by rw [Metric.infDist_zero_of_mem hx]; exact hρ)
    rw [dist_eq_norm, norm_sub_rev] at h2
    linarith

/-- Local ambient equivalence is constant on a connected parameter space. -/
theorem family_motion_of_local {ι α : Type*} [TopologicalSpace α] [PreconnectedSpace α]
    (C : α → ι → Set Space3)
    (hloc : ∀ a, ∀ᶠ b in 𝓝 a, FamilyMotion (C a) (C b)) (a b : α) :
    FamilyMotion (C a) (C b) := by
  let S : Set α := {x | FamilyMotion (C a) (C x)}
  have hopen : IsOpen S := isOpen_iff_mem_nhds.2 (by
    intro x hx
    exact Filter.mem_of_superset (hloc x) (fun y hy => hx.trans hy))
  have hcomp : IsOpen Sᶜ := isOpen_iff_mem_nhds.2 (by
    intro x hx
    exact Filter.mem_of_superset (hloc x) (fun y hy h => hx (h.trans hy.symm)))
  have hcl : IsClopen S := ⟨by simpa using hcomp.isClosed_compl, hopen⟩
  have heq : S = Set.univ := hcl.eq_univ ⟨a, FamilyMotion.refl (C a)⟩
  have : b ∈ S := heq ▸ Set.mem_univ b
  exact this

theorem small_affine_family_motion {ι : Type*} [Fintype ι]
    (C : ι → Set Space3) (hc : ∀ i, IsCompact (C i)) (hne : ∀ i, (C i).Nonempty)
    (hd : ∀ i j, i ≠ j → Disjoint (C i) (C j)) :
    ∃ ε > 0, ∀ (Q : ι → Matrix (Fin 3) (Fin 3) ℝ) (q : ι → Space3),
      (∀ i a b, |(Q i - 1) a b| ≤ ε) → (∀ i, ‖q i‖ ≤ ε) →
      FamilyMotion C (fun i => (fun x => Q i *ᵥ x + q i) '' C i) := by
  obtain ⟨ρ, hρ, hsep⟩ := compact_family_separation C hc hne hd
  have hU : IsCompact (⋃ i, C i) := isCompact_iUnion hc
  obtain ⟨R0, hR0⟩ := hU.isBounded.exists_norm_le
  let R := max R0 0 + ρ
  have hR : 0 ≤ R := by positivity
  have hnear : ∀ i y, Metric.infDist y (C i) < ρ → ‖y‖ ≤ R := by
    intro i y hy
    obtain ⟨x, hx, hxy⟩ := (Metric.infDist_lt_iff (hne i)).1 hy
    have hxR := hR0 x (Set.mem_iUnion.2 ⟨i, hx⟩)
    rw [dist_eq_norm] at hxy
    calc ‖y‖ = ‖(y - x) + x‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ R := by dsimp [R]; linarith [le_max_left R0 0]
  let ε := min (1 / 12) (ρ / (4 * (3 * R + 1)))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  refine ⟨ε, hε, fun Q q hQ hq => ?_⟩
  have hε12 : ε ≤ 1 / 12 := min_le_left _ _
  have hεR : ε * (3 * R + 1) ≤ ρ / 4 := by
    calc ε * (3 * R + 1) ≤ ρ / (4 * (3 * R + 1)) * (3 * R + 1) := by
          gcongr; exact min_le_right _ _
      _ = ρ / 4 := by field_simp
  apply simultaneous_small_step C hne ρ hρ hsep (fun i x => Q i *ᵥ x + q i)
    (fun i => by fun_prop)
  · intro i x y
    have he : (Q i *ᵥ x + q i - x) - (Q i *ᵥ y + q i - y) =
        (Q i - 1) *ᵥ (x - y) := by
      simp only [Matrix.sub_mulVec, Matrix.mulVec_sub, Matrix.one_mulVec]
      abel
    rw [he]
    calc _ ≤ 3 * ε * ‖x - y‖ := mulVec_bound _ ε (hQ i) _
      _ ≤ 1 / 4 * ‖x - y‖ := by gcongr; linarith
  · intro i y hy
    have he : Q i *ᵥ y + q i - y = (Q i - 1) *ᵥ y + q i := by
      simp only [Matrix.sub_mulVec, Matrix.one_mulVec]
      abel
    rw [he]
    calc _ ≤ ‖(Q i - 1) *ᵥ y‖ + ‖q i‖ := norm_add_le _ _
      _ ≤ 3 * ε * R + ε := add_le_add
        ((mulVec_bound _ ε (hQ i) y).trans (by gcongr; exact hnear i y hy)) (hq i)
      _ ≤ ρ / 4 := by nlinarith

/-- Ambient isotopy extension for a finite family following separate invertible
affine paths, assuming their images stay pairwise disjoint. -/
theorem affine_family_motion {ι : Type*} [Fintype ι]
    (E : ι → Set Space3) (hE : ∀ i, IsCompact (E i)) (hne : ∀ i, (E i).Nonempty)
    (M : ι → ℝ → Matrix (Fin 3) (Fin 3) ℝ) (b : ι → ℝ → Space3)
    (hM : ∀ i, Continuous (M i)) (hb : ∀ i, Continuous (b i))
    (hdet : ∀ i t, (M i t).det ≠ 0)
    (hdisj : ∀ t i j, i ≠ j →
      Disjoint ((fun x => M i t *ᵥ x + b i t) '' E i)
        ((fun x => M j t *ᵥ x + b j t) '' E j)) (s t : ℝ) :
    FamilyMotion (fun i => (fun x => M i s *ᵥ x + b i s) '' E i)
      (fun i => (fun x => M i t *ᵥ x + b i t) '' E i) := by
  classical
  apply family_motion_of_local (fun s i => (fun x => M i s *ᵥ x + b i s) '' E i) ?_ s t
  intro a
  let C : ι → Set Space3 := fun i => (fun x => M i a *ᵥ x + b i a) '' E i
  obtain ⟨ε, hε, hsmall⟩ := small_affine_family_motion C
    (fun i => (hE i).image (by fun_prop)) (fun i => (hne i).image _)
    (hdisj a)
  let N : ι → Matrix (Fin 3) (Fin 3) ℝ := fun i => (M i a)⁻¹
  have hMN : ∀ i, M i a * N i = 1 := fun i =>
    Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (hdet i a))
  have hNM : ∀ i, N i * M i a = 1 := fun i =>
    Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet i a))
  let Q : ℝ → ι → Matrix (Fin 3) (Fin 3) ℝ := fun s i => M i s * N i
  let q : ℝ → ι → Space3 := fun s i => b i s - Q s i *ᵥ b i a
  let Ψ : ℝ → ι → (Fin 3 → Fin 3 → ℝ) × Space3 :=
    fun s i => (fun j k => Q s i j k, q s i)
  have hΨc : Continuous Ψ := by
    apply continuous_pi
    intro i
    have hQc : Continuous (fun s => Q s i) := (hM i).matrix_mul continuous_const
    exact (continuous_pi fun j => continuous_pi fun k => hQc.matrix_elem j k).prodMk
      ((hb i).sub (hQc.matrix_mulVec continuous_const))
  have hΨa : ∀ i, Ψ a i = (fun j k => (1 : Matrix (Fin 3) (Fin 3) ℝ) j k, 0) := by
    intro i
    simp only [Ψ, Q, q, hMN, Matrix.one_mulVec, sub_self]
  have hevent : ∀ᶠ p in 𝓝 a, dist (Ψ p) (Ψ a) < ε :=
    hΨc.continuousAt.eventually (Metric.ball_mem_nhds (Ψ a) hε)
  filter_upwards [hevent] with p hp
  have hQi : ∀ i a b, |(Q p i - 1) a b| ≤ ε := by
    intro i j k
    have hi := (dist_le_pi_dist (Ψ p) (Ψ a) i).trans_lt hp
    rw [hΨa, Prod.dist_eq, max_lt_iff] at hi
    have hh := (dist_le_pi_dist _ _ k).trans ((dist_le_pi_dist _ _ j).trans hi.1.le)
    simpa [Real.dist_eq, Matrix.sub_apply] using hh
  have hqi : ∀ i, ‖q p i‖ ≤ ε := by
    intro i
    have hi := (dist_le_pi_dist (Ψ p) (Ψ a) i).trans_lt hp
    rw [hΨa, Prod.dist_eq, max_lt_iff] at hi
    simpa only [Ψ, dist_zero_right] using hi.2.le
  have hm := hsmall (Q p) (q p) hQi hqi
  have himg : (fun i => (fun x => Q p i *ᵥ x + q p i) '' C i) =
      (fun i => (fun x => M i p *ᵥ x + b i p) '' E i) := by
    funext i
    dsimp only [C]
    rw [← Set.image_comp]
    apply Set.image_congr
    intro x _
    dsimp only [Function.comp_def, q, Q]
    simp only [Matrix.mulVec_add, Matrix.mulVec_mulVec]
    rw [Matrix.mul_assoc, hNM, Matrix.mul_one]
    abel
  rw [himg] at hm
  exact hm

end BookCircleCompletion

/- Source module: GenericPosition -/

noncomputable section
namespace BookCircleCompletion
open BookSixth Matrix F494 Set

theorem CircleData.curve_compact (D : CircleData) (s : ℝ) : IsCompact (D.curve s) :=
  Function.Periodic.compact_of_continuous (c := 2 * Real.pi)
    (D.point_periodic s) (by positivity) (D.point_continuous s)

theorem CircleData.curve_nonempty (D : CircleData) (s : ℝ) : (D.curve s).Nonempty :=
  Set.range_nonempty _

def CircleData.shift (D : CircleData) (w : Space3) : CircleData := {D with c := D.c + w}

theorem CircleData.curve_shift (D : CircleData) (w : Space3) (s : ℝ) :
    (D.shift w).curve s = (fun x => x + w) '' D.curve s := by
  simp only [CircleData.curve, ← Set.range_comp]
  apply congrArg Set.range
  funext t
  dsimp [CircleData.point, CircleData.shift, Function.comp_def]
  abel

def dotLinear (n : Space3) : Module.Dual ℝ Space3 where
  toFun x := n ⬝ᵥ x
  map_add' x y := dotProduct_add _ _ _
  map_smul' r x := by simp

/-- Arbitrarily small translations put centres off all the other circle
planes, and give the centres pairwise distinct first coordinates. -/
theorem generic_circle_position {m : ℕ} (D : Fin m → CircleData)
    (hd : ∀ i j, i ≠ j → Disjoint ((D i).curve (D i).r) ((D j).curve (D j).r)) :
    ∃ E : Fin m → CircleData,
      FamilyMotion (fun i => (D i).curve (D i).r) (fun i => (E i).curve (E i).r) ∧
      (∀ i j, i ≠ j → (E j).normal ⬝ᵥ ((E i).c - (E j).c) ≠ 0) ∧
      (∀ i j, i ≠ j → (E i).c 0 ≠ (E j).c 0) := by
  classical
  let n : Option (Fin m) → Space3 := fun k => match k with
    | none => ![1, 0, 0]
    | some i => (D i).normal
  have hn : ∀ k, n k ⬝ᵥ n k = 1 := by
    intro k
    cases k with
    | none => norm_num [n, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
    | some i => exact (D i).normal_unit
  obtain ⟨v, hv⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
    (fun k => dotLinear (n k)) (fun k => ⟨n k, by change n k ⬝ᵥ n k ≠ 0; rw [hn]; norm_num⟩)
  change ∀ k, n k ⬝ᵥ v ≠ 0 at hv
  obtain ⟨ε, hε, hsmall⟩ := small_affine_family_motion
    (fun i => (D i).curve (D i).r) (fun i => (D i).curve_compact _)
    (fun i => (D i).curve_nonempty _) hd
  let L : ℝ := (m + 1) * (‖v‖ + 1)
  have hL : 0 < L := by dsimp [L]; positivity
  let bad : Fin m × Fin m × Option (Fin m) → ℝ := fun p =>
    -(n p.2.2 ⬝ᵥ ((D p.1).c - (D p.2.1).c)) /
      (((p.1 : ℝ) - (p.2.1 : ℝ)) * (n p.2.2 ⬝ᵥ v))
  obtain ⟨δ, hδ, hδbad⟩ := (Set.Ioo_infinite (div_pos hε hL)).exists_notMem_finite
    (Set.finite_range bad)
  let w : Fin m → Space3 := fun i => (δ * (i : ℝ)) • v
  let E : Fin m → CircleData := fun i => (D i).shift (w i)
  have hw : ∀ i, ‖w i‖ ≤ ε := by
    intro i
    simp only [w, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hδ.1.le (Nat.cast_nonneg i.val))]
    have hi : (i : ℝ) ≤ (m : ℝ) + 1 := by
      have hi' : (i : ℝ) < m := by exact_mod_cast i.isLt
      linarith
    have hδL : δ * L < ε := (lt_div_iff₀ hL).1 hδ.2
    calc δ * (i : ℝ) * ‖v‖ ≤ δ * ((m : ℝ) + 1) * (‖v‖ + 1) := by
          exact mul_le_mul (mul_le_mul_of_nonneg_left hi hδ.1.le)
            (le_add_of_nonneg_right zero_le_one) (norm_nonneg v)
            (mul_nonneg hδ.1.le (by positivity))
      _ = δ * L := by dsimp [L]; ring
      _ ≤ ε := hδL.le
  have heq : ∀ i j, i ≠ j → ∀ k, n k ⬝ᵥ ((E i).c - (E j).c) ≠ 0 := by
    intro i j hij k hzero
    have hcast : (i : ℝ) - (j : ℝ) ≠ 0 := by
      apply sub_ne_zero.2
      intro h
      apply hij
      apply Fin.ext
      exact_mod_cast h
    have hden : ((i : ℝ) - (j : ℝ)) * (n k ⬝ᵥ v) ≠ 0 := mul_ne_zero hcast (hv k)
    have hz : n k ⬝ᵥ ((D i).c - (D j).c) +
        δ * (((i : ℝ) - (j : ℝ)) * (n k ⬝ᵥ v)) = 0 := by
      dsimp [E, CircleData.shift, w] at hzero
      simp only [dotProduct_sub, dotProduct_add, dotProduct_smul, smul_eq_mul] at hzero ⊢
      linear_combination hzero
    have hb : bad (i, j, k) = δ := by
      dsimp [bad]
      apply (div_eq_iff hden).2
      linarith
    exact hδbad ⟨(i, j, k), hb⟩
  refine ⟨E, ?_, ?_, ?_⟩
  · have hm := hsmall (fun _ => 1) w (by intros; simp; exact hε.le) hw
    have ht : (fun i => (fun x => (1 : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ x + w i) ''
        (D i).curve (D i).r) = (fun i => (E i).curve (E i).r) := by
      funext i
      simp only [Matrix.one_mulVec, E, CircleData.shift]
      exact ((D i).curve_shift (w i) (D i).r).symm
    rw [ht] at hm
    exact hm
  · intro i j hij
    exact heq i j hij (some j)
  · intro i j hij h
    have hn0 := heq i j hij none
    apply hn0
    simpa [n, dotProduct, Fin.sum_univ_three, h]

end BookCircleCompletion

/- Source module: FrozenShrink -/

noncomputable section
namespace BookCircleCompletion
open BookSixth Matrix F494 Set

theorem unit_dot_abs_le_one (u v : Space3) (hu : u ⬝ᵥ u = 1) (hv : v ⬝ᵥ v = 1) :
    |u ⬝ᵥ v| ≤ 1 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  simp only [sq] at h
  change (u ⬝ᵥ v) * (u ⬝ᵥ v) ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) at h
  rw [hu, hv] at h
  rw [← sq_le_one_iff_abs_le_one]
  nlinarith only [h]

theorem small_circle_avoids_plane (D E : CircleData) (ε : ℝ) (hε : 0 ≤ ε)
    (hsep : ε < |E.normal ⬝ᵥ (D.c - E.c)|) (θ : ℝ) :
    E.normal ⬝ᵥ (D.point ε θ - E.c) ≠ 0 := by
  intro hz
  have he : D.point ε θ - E.c = D.c - E.c +
      ε • (Real.cos θ • D.u + Real.sin θ • D.v) := by
    dsimp [CircleData.point]
    abel
  rw [he, dotProduct_add, dotProduct_smul, smul_eq_mul] at hz
  have hw := unit_dot_abs_le_one E.normal (Real.cos θ • D.u + Real.sin θ • D.v)
    E.normal_unit (D.direction_unit θ)
  have hb : |E.normal ⬝ᵥ (D.c - E.c)| ≤ ε := by
    rw [show E.normal ⬝ᵥ (D.c - E.c) =
      -ε * (E.normal ⬝ᵥ (Real.cos θ • D.u + Real.sin θ • D.v)) by linarith,
      abs_mul, abs_neg, abs_of_nonneg hε]
    simpa using mul_le_mul_of_nonneg_left hw hε
  linarith

theorem radii_family_motion {ι : Type*} [Fintype ι] (D : ι → CircleData)
    (ρ : ι → ℝ → ℝ) (hρc : ∀ i, Continuous (ρ i)) (hρ : ∀ i t, 0 < ρ i t)
    (hdisj : ∀ t i j, i ≠ j → Disjoint ((D i).curve (ρ i t)) ((D j).curve (ρ j t)))
    (s t : ℝ) : FamilyMotion (fun i => (D i).curve (ρ i s))
      (fun i => (D i).curve (ρ i t)) := by
  let M : ι → ℝ → Matrix (Fin 3) (Fin 3) ℝ := fun i t => ρ i t • 1
  let b : ι → ℝ → Space3 := fun i t => (D i).c - ρ i t • (D i).c
  have himg : ∀ t i, (fun x => M i t *ᵥ x + b i t) '' (D i).curve 1 =
      (D i).curve (ρ i t) := by
    intro t i
    simp only [CircleData.curve, ← Set.range_comp]
    apply congrArg Set.range
    funext θ
    dsimp [Function.comp_def, M, b, CircleData.point]
    simp only [Matrix.smul_mulVec, Matrix.one_mulVec, one_smul]
    module
  have hm := affine_family_motion (fun i => (D i).curve 1)
    (fun i => (D i).curve_compact _) (fun i => (D i).curve_nonempty _) M b
    (fun i => (hρc i).smul continuous_const) (fun i => by dsimp [b]; fun_prop)
    (by intro i t; simp only [M, Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one]
        exact pow_ne_zero _ (hρ i t).ne')
    (by intro t i j hij; simpa only [himg] using hdisj t i j hij) s t
  simpa only [himg] using hm

theorem frozen_shrink_motion {m : ℕ} (D : Fin m → CircleData)
    (hpairs : ∀ i j, i ≠ j →
      IsUnlink (![(D i).curve (D i).r, (D j).curve (D j).r] : Fin 2 → Set Space3))
    (ε : ℝ) (hε : 0 < ε) (her : ∀ i, ε < (D i).r)
    (heplane : ∀ i j, i ≠ j → ε < |(D j).normal ⬝ᵥ ((D i).c - (D j).c)|) :
    FamilyMotion (fun i => (D i).curve (D i).r) (fun i => (D i).curve ε) := by
  classical
  let ρ : Fin m → ℝ → ℝ := fun i t => Real.sqrt (max ((D i).r ^ 2 - max 0 t) (ε ^ 2))
  have hρpos : ∀ i t, 0 < ρ i t := by
    intro i t
    apply Real.sqrt_pos.2
    exact (sq_pos_of_pos hε).trans_le (le_max_right _ _)
  have hρsq : ∀ i t, (ρ i t) ^ 2 = max ((D i).r ^ 2 - max 0 t) (ε ^ 2) := by
    intro i t
    apply Real.sq_sqrt
    exact (sq_nonneg ε).trans (le_max_right _ _)
  have hρzero : ∀ i, ρ i 0 = (D i).r := by
    intro i
    dsimp [ρ]
    rw [max_self, sub_zero, max_eq_left (by nlinarith [her i, (D i).hr]),
      Real.sqrt_sq_eq_abs, abs_of_pos (D i).hr]
  have hfrozen : ∀ i t, (D i).r ^ 2 - max 0 t ≤ ε ^ 2 → ρ i t = ε := by
    intro i t h
    dsimp [ρ]
    rw [max_eq_right h, Real.sqrt_sq_eq_abs, abs_of_pos hε]
  have hd : ∀ t i j, i ≠ j → Disjoint ((D i).curve (ρ i t)) ((D j).curve (ρ j t)) := by
    intro t i j hij
    by_cases hi : (D i).r ^ 2 - max 0 t ≤ ε ^ 2
    · rw [hfrozen i t hi, Set.disjoint_left]
      rintro x ⟨θ, hθ⟩ ⟨φ, hφ⟩
      apply small_circle_avoids_plane (D i) (D j) ε hε.le (heplane i j hij) θ
      rw [hθ, ← hφ]
      exact (D j).point_plane _ _
    by_cases hj : (D j).r ^ 2 - max 0 t ≤ ε ^ 2
    · rw [hfrozen j t hj, Set.disjoint_left]
      rintro x ⟨θ, hθ⟩ ⟨φ, hφ⟩
      apply small_circle_avoids_plane (D j) (D i) ε hε.le (heplane j i hij.symm) φ
      rw [hφ, ← hθ]
      exact (D i).point_plane _ _
    exact canonical_shrink_disjoint (D i) (D j) (hpairs i j hij) (max 0 t)
      (ρ i t) (ρ j t) (le_max_left _ _)
      (by rw [hρsq, max_eq_left (le_of_not_ge hi)])
      (by rw [hρsq, max_eq_left (le_of_not_ge hj)])
  let T : ℝ := ∑ i, (D i).r ^ 2
  have hρend : ∀ i, ρ i T = ε := by
    intro i
    apply hfrozen
    have hi : (D i).r ^ 2 ≤ T := Finset.single_le_sum (fun j _ => sq_nonneg (D j).r)
      (Finset.mem_univ i)
    have hT : T ≤ max 0 T := le_max_right _ _
    nlinarith [sq_nonneg ε]
  have hm := radii_family_motion D ρ (fun i => by dsimp [ρ]; fun_prop) hρpos hd 0 T
  simpa only [hρzero, hρend] using hm

end BookCircleCompletion

/- Source module: Endgame -/

noncomputable section
namespace BookCircleCompletion
open BookSixth Matrix F494 Set

def xy (t : ℝ) : Space3 := ![Real.cos t, Real.sin t, 0]

def horizontalCircle (c : Space3) (r : ℝ) : Set Space3 := Set.range (fun t => c + r • xy t)

theorem xy_continuous : Continuous xy := by unfold xy; fun_prop

theorem coordinate_disjoint (C D : Set Space3) (a b r s : ℝ)
    (hC : ∀ x ∈ C, |x 0 - a| ≤ r) (hD : ∀ x ∈ D, |x 0 - b| ≤ s)
    (hsep : r + s < |a - b|) : Disjoint C D := by
  rw [Set.disjoint_left]
  intro x hx hy
  have h1 := hC x hx
  have h2 := hD x hy
  have h3 : |a - b| ≤ r + s := by
    calc |a - b| = |(a - x 0) + (x 0 - b)| := by congr 1; ring
      _ ≤ |a - x 0| + |x 0 - b| := by
        simpa only [Real.norm_eq_abs] using norm_add_le (a - x 0) (x 0 - b)
      _ ≤ r + s := add_le_add (by simpa only [abs_sub_comm] using h1) h2
  linarith

theorem horizontal_x_bound (c : Space3) (r : ℝ) (hr : 0 ≤ r) :
    ∀ x ∈ horizontalCircle c r, |x 0 - c 0| ≤ r := by
  rintro x ⟨θ, rfl⟩
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, xy, Matrix.cons_val_zero,
    add_sub_cancel_left, abs_mul, abs_of_nonneg hr]
  simpa using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) hr

theorem horizontal_z_disjoint (c d : Space3) (r s : ℝ) (hz : c 2 ≠ d 2) :
    Disjoint (horizontalCircle c r) (horizontalCircle d s) := by
  rw [Set.disjoint_left]
  rintro x ⟨θ, hθ⟩ ⟨φ, hφ⟩
  have hh := congrFun (hθ.trans hφ.symm) 2
  apply hz
  simpa [xy, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using hh

theorem horizontal_family_motion {ι : Type*} [Fintype ι]
    (c : ι → ℝ → Space3) (r : ι → ℝ → ℝ)
    (hc : ∀ i, Continuous (c i)) (hrc : ∀ i, Continuous (r i)) (hr : ∀ i t, 0 < r i t)
    (hd : ∀ t i j, i ≠ j → Disjoint (horizontalCircle (c i t) (r i t))
      (horizontalCircle (c j t) (r j t))) (s t : ℝ) :
    FamilyMotion (fun i => horizontalCircle (c i s) (r i s))
      (fun i => horizontalCircle (c i t) (r i t)) := by
  have hcomp : IsCompact (Set.range xy) :=
    Function.Periodic.compact_of_continuous (c := 2 * Real.pi)
      (fun t => by simp [xy, Real.cos_add_two_pi, Real.sin_add_two_pi])
      (by positivity) xy_continuous
  have himg : ∀ t i, (fun x => (r i t • (1 : Matrix (Fin 3) (Fin 3) ℝ)) *ᵥ x + c i t) ''
      Set.range xy = horizontalCircle (c i t) (r i t) := by
    intro t i
    rw [← Set.range_comp]
    apply congrArg Set.range
    funext θ
    simp [horizontalCircle, Function.comp_def, Matrix.smul_mulVec, add_comm]
  have hm := affine_family_motion (fun _ : ι => Set.range xy) (fun _ => hcomp)
    (fun _ => Set.range_nonempty _) (fun i t => r i t • 1) c
    (fun i => (hrc i).smul continuous_const) hc
    (by intro i t; simp only [Matrix.det_smul, Fintype.card_fin, Matrix.det_one, mul_one]
        exact pow_ne_zero _ (hr i t).ne')
    (by intro t i j hij; simpa only [himg] using hd t i j hij) s t
  simpa only [himg] using hm

theorem rotate_small_circles {m : ℕ} (D : Fin m → CircleData) (ε : ℝ) (hε : 0 < ε)
    (hsep : ∀ i j, i ≠ j → 2 * ε < |(D i).c 0 - (D j).c 0|) :
    FamilyMotion (fun i => (D i).curve ε) (fun i => horizontalCircle (D i).c ε) := by
  classical
  have hframes : ∀ i, ∃ θ1 θ2 θ3 : ℝ, ∀ t,
      R12 θ3 *ᵥ (R02 θ2 *ᵥ (R01 θ1 *ᵥ
        (Real.cos t • (D i).u + Real.sin t • (D i).v))) = xy t := by
    intro i
    apply frame57
    · simpa only [dotProduct, Fin.sum_univ_three] using (D i).hu
    · simpa only [dotProduct, Fin.sum_univ_three] using (D i).hv
    · simpa only [dotProduct, Fin.sum_univ_three] using (D i).huv
  choose θ1 θ2 θ3 hframe using hframes
  let M : Fin m → ℝ → Matrix (Fin 3) (Fin 3) ℝ :=
    fun i s => R12 (s * θ3 i) * R02 (s * θ2 i) * R01 (s * θ1 i)
  let b : Fin m → ℝ → Space3 := fun i s => (D i).c - M i s *ᵥ (D i).c
  have hM : ∀ i, Continuous (M i) := fun i =>
    ((R12_cont (θ3 i)).matrix_mul (R02_cont (θ2 i))).matrix_mul (R01_cont (θ1 i))
  have hMapply : ∀ i s x, M i s *ᵥ x = R12 (s * θ3 i) *ᵥ
      (R02 (s * θ2 i) *ᵥ (R01 (s * θ1 i) *ᵥ x)) := by
    intros
    simp only [M, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have hnorm : ∀ i s x, sumsq (M i s *ᵥ x) = sumsq x := by
    intros
    rw [hMapply, sumsq_R12, sumsq_R02, sumsq_R01]
  have hform : ∀ i s t, M i s *ᵥ (D i).point ε t + b i s =
      (D i).c + ε • (M i s *ᵥ (Real.cos t • (D i).u + Real.sin t • (D i).v)) := by
    intros
    dsimp [CircleData.point, b]
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
    module
  have hbound : ∀ i s, ∀ x ∈ (fun x => M i s *ᵥ x + b i s) '' (D i).curve ε,
      |x 0 - (D i).c 0| ≤ ε := by
    rintro i s x ⟨_, ⟨t, rfl⟩, rfl⟩
    change |(M i s *ᵥ (D i).point ε t + b i s) 0 - (D i).c 0| ≤ ε
    rw [hform]
    have hn : sumsq (M i s *ᵥ (Real.cos t • (D i).u + Real.sin t • (D i).v)) = 1 := by
      rw [hnorm]
      simpa only [sumsq, dotProduct, Fin.sum_univ_three, pow_two] using (D i).direction_unit t
    let y := M i s *ᵥ (Real.cos t • (D i).u + Real.sin t • (D i).v)
    have hy : |y 0| ≤ 1 := by
      rw [← sq_le_one_iff_abs_le_one]
      change y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 = 1 at hn
      nlinarith [sq_nonneg (y 1), sq_nonneg (y 2)]
    change |((D i).c + ε • y) 0 - (D i).c 0| ≤ ε
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left,
      abs_mul, abs_of_pos hε]
    simpa using mul_le_mul_of_nonneg_left hy hε.le
  have hzero : ∀ i, (fun x => M i 0 *ᵥ x + b i 0) '' (D i).curve ε = (D i).curve ε := by
    intro i
    simp [M, b, R12_zero, R02_zero, R01_zero]
  have hone : ∀ i, (fun x => M i 1 *ᵥ x + b i 1) '' (D i).curve ε =
      horizontalCircle (D i).c ε := by
    intro i
    simp only [CircleData.curve, horizontalCircle, ← Set.range_comp]
    apply congrArg Set.range
    funext t
    change M i 1 *ᵥ (D i).point ε t + b i 1 = _
    rw [hform, hMapply]
    simp only [one_mul, hframe]
  have hm := affine_family_motion (fun i => (D i).curve ε)
    (fun i => (D i).curve_compact _) (fun i => (D i).curve_nonempty _) M b hM
    (fun i => by dsimp [b]; exact continuous_const.sub ((hM i).matrix_mulVec continuous_const))
    (by intro i s; simp only [M, Matrix.det_mul, R12_det, R02_det, R01_det]; norm_num)
    (by intro s i j hij
        exact coordinate_disjoint _ _ _ _ ε ε (hbound i s) (hbound j s) (by linarith [hsep i j hij]))
    0 1
  simpa only [hzero, hone] using hm

theorem slot_separation {m : ℕ} (i j : Fin m) (hij : i ≠ j) :
    3 ≤ |3 * (i : ℝ) - 3 * (j : ℝ)| := by
  rcases lt_trichotomy i.val j.val with h | h | h
  · have hh : (i : ℝ) + 1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_nonpos (by linarith)]
    linarith
  · exact (hij (Fin.ext h)).elim
  · have hh : (j : ℝ) + 1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
    rw [abs_of_nonneg (by linarith)]
    linarith

theorem horizontal_standard (i : ℕ) :
    horizontalCircle ![3 * (i : ℝ), 0, 0] 1 = standardCircle i := by
  apply congrArg Set.range
  funext t
  ext k
  fin_cases k <;> simp [xy, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

theorem horizontal_endgame {m : ℕ} (c : Fin m → Space3) (ε : ℝ)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsep : ∀ i j, i ≠ j → 2 * ε < |c i 0 - c j 0|) :
    IsUnlink (fun i => horizontalCircle (c i) ε) := by
  let high : Fin m → Space3 := fun i => ![c i 0, c i 1, 3 * (i : ℝ)]
  let slot : Fin m → Space3 := fun i => ![3 * (i : ℝ), 0, 3 * (i : ℝ)]
  let c1 : Fin m → ℝ → Space3 := fun i s =>
    ![c i 0, c i 1, (1 - s) * c i 2 + s * (3 * (i : ℝ))]
  have hc10 : ∀ i, c1 i 0 = c i := by
    intro i
    ext k
    fin_cases k <;> simp [c1, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hc11 : ∀ i, c1 i 1 = high i := by
    intro i
    simp [c1, high]
  have step1 : FamilyMotion (fun i => horizontalCircle (c i) ε)
      (fun i => horizontalCircle (high i) ε) := by
    have hm := horizontal_family_motion c1 (fun _ _ => ε)
      (fun i => by dsimp [c1]; fun_prop) (fun _ => continuous_const) (fun _ _ => hε)
      (by
        intro s i j hij
        apply coordinate_disjoint _ _ (c i 0) (c j 0) ε ε
        · exact horizontal_x_bound (c1 i s) ε hε.le
        · exact horizontal_x_bound (c1 j s) ε hε.le
        · linarith [hsep i j hij]) 0 1
    simpa only [hc10, hc11] using hm
  let c2 : Fin m → ℝ → Space3 := fun i s =>
    ![(1 - s) * c i 0 + s * (3 * (i : ℝ)), (1 - s) * c i 1, 3 * (i : ℝ)]
  have hc20 : ∀ i, c2 i 0 = high i := by intro i; simp [c2, high]
  have hc21 : ∀ i, c2 i 1 = slot i := by intro i; simp [c2, slot]
  have step2 : FamilyMotion (fun i => horizontalCircle (high i) ε)
      (fun i => horizontalCircle (slot i) ε) := by
    have hm := horizontal_family_motion c2 (fun _ _ => ε)
      (fun i => by dsimp [c2]; fun_prop) (fun _ => continuous_const) (fun _ _ => hε)
      (by
        intro s i j hij
        apply horizontal_z_disjoint
        have h := slot_separation i j hij
        intro he
        change 3 * (i : ℝ) = 3 * (j : ℝ) at he
        rw [he, sub_self, abs_zero] at h
        linarith) 0 1
    simpa only [hc20, hc21] using hm
  let κ : ℝ → ℝ := fun s => max 0 (min s 1)
  have hκ0 : ∀ s, 0 ≤ κ s := fun s => le_max_left _ _
  have hκ1 : ∀ s, κ s ≤ 1 := fun s => max_le zero_le_one (min_le_right _ _)
  let ρ : ℝ → ℝ := fun s => ε + κ s * (1 - ε)
  have hρpos : ∀ s, 0 < ρ s := by
    intro s
    have := mul_nonneg (hκ0 s) (sub_nonneg.2 hε1)
    dsimp [ρ]
    linarith
  have hρ1 : ∀ s, ρ s ≤ 1 := by
    intro s
    have := mul_le_mul_of_nonneg_right (hκ1 s) (sub_nonneg.2 hε1)
    dsimp [ρ]
    linarith
  have hr0 : ρ 0 = ε := by simp [ρ, κ]
  have hr1 : ρ 1 = 1 := by simp [ρ, κ]
  let c3 : Fin m → ℝ → Space3 := fun i s => ![3 * (i : ℝ), 0, (1 - s) * (3 * (i : ℝ))]
  have hc30 : ∀ i, c3 i 0 = slot i := by intro i; simp [c3, slot]
  have hc31 : ∀ i, c3 i 1 = ![3 * (i : ℝ), 0, 0] := by intro i; simp [c3]
  have step3 : FamilyMotion (fun i => horizontalCircle (slot i) ε)
      (fun i => standardCircle i.val) := by
    have hm := horizontal_family_motion c3 (fun _ => ρ)
      (fun i => by dsimp [c3]; fun_prop) (fun _ => by dsimp [ρ, κ]; fun_prop)
      (fun _ => hρpos)
      (by
        intro s i j hij
        apply coordinate_disjoint _ _ (3 * (i : ℝ)) (3 * (j : ℝ)) (ρ s) (ρ s)
        · exact horizontal_x_bound (c3 i s) (ρ s) (hρpos s).le
        · exact horizontal_x_bound (c3 j s) (ρ s) (hρpos s).le
        · linarith [slot_separation i j hij, hρ1 s]) 0 1
    simpa only [hr0, hr1, hc30, hc31, horizontal_standard] using hm
  exact step1.trans (step2.trans step3)

end BookCircleCompletion

/- Source module: Completion -/

noncomputable section
namespace BookCircleCompletion
open BookSixth Matrix F494 Set

theorem safe_common_radius {m : ℕ} (D : Fin m → CircleData)
    (hp : ∀ i j, i ≠ j → (D j).normal ⬝ᵥ ((D i).c - (D j).c) ≠ 0)
    (hx : ∀ i j, i ≠ j → (D i).c 0 ≠ (D j).c 0) :
    ∃ ε > 0, ε ≤ 1 ∧ (∀ i, ε < (D i).r) ∧
      (∀ i j, i ≠ j → ε < |(D j).normal ⬝ᵥ ((D i).c - (D j).c)|) ∧
      (∀ i j, i ≠ j → 2 * ε < |(D i).c 0 - (D j).c 0|) := by
  classical
  obtain ⟨R, hR, hRi⟩ := finite_positive_lower_bound (fun i => (D i).r) (fun i => (D i).hr)
  let p : Fin m × Fin m → ℝ := fun q => if q.1 = q.2 then 1 else
    |(D q.2).normal ⬝ᵥ ((D q.1).c - (D q.2).c)|
  have hpp : ∀ q, 0 < p q := by
    intro q
    dsimp [p]
    split_ifs with h
    · exact one_pos
    · exact abs_pos.2 (hp q.1 q.2 h)
  obtain ⟨P, hP, hPi⟩ := finite_positive_lower_bound p hpp
  let x : Fin m × Fin m → ℝ := fun q => if q.1 = q.2 then 1 else |(D q.1).c 0 - (D q.2).c 0|
  have hxp : ∀ q, 0 < x q := by
    intro q
    dsimp [x]
    split_ifs with h
    · exact one_pos
    · exact abs_pos.2 (sub_ne_zero.2 (hx q.1 q.2 h))
  obtain ⟨X, hX, hXi⟩ := finite_positive_lower_bound x hxp
  let ε := min (R / 2) (min (P / 2) (min (X / 4) (1 / 4)))
  have hε : 0 < ε := by dsimp [ε]; positivity
  have heR : ε ≤ R / 2 := min_le_left _ _
  have heP : ε ≤ P / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have heX : ε ≤ X / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _))
  have he1 : ε ≤ 1 / 4 := (min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_right _ _))
  refine ⟨ε, hε, by linarith, fun i => by linarith [hRi i], ?_, ?_⟩
  · intro i j hij
    have h := hPi (i, j)
    simp only [p, if_neg hij] at h
    linarith
  · intro i j hij
    have h := hXi (i, j)
    simp only [x, if_neg hij] at h
    linarith

/-- The pairwise unlinking theorem for finite families of round circles. -/
theorem round_circle_unlink {m : ℕ} (C : Fin m → Set Space3)
    (hround : ∀ i, RoundCircle (C i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hpairs : ∀ i j, i ≠ j → IsUnlink (![C i, C j] : Fin 2 → Set Space3)) :
    IsUnlink C := by
  classical
  choose D hD using fun i => circleData_of_round (hround i)
  obtain ⟨E, hDE, hplane, hx⟩ := generic_circle_position D
    (fun i j hij => by simpa only [hD] using hdisjoint i j hij)
  have hEpairs : ∀ i j, i ≠ j →
      IsUnlink (![(E i).curve (E i).r, (E j).curve (E j).r] : Fin 2 → Set Space3) := by
    intro i j hij
    apply (hDE.symm.pair i j).isUnlink
    simpa only [hD] using hpairs i j hij
  obtain ⟨ε, hε, hε1, hεr, hεplane, hεsep⟩ := safe_common_radius E hplane hx
  have hshrink := frozen_shrink_motion E hEpairs ε hε hεr hεplane
  have hrotate := rotate_small_circles E ε hε hεsep
  have hfinal := horizontal_endgame (fun i => (E i).c) ε hε hε1 hεsep
  have hDunlink := hDE.isUnlink (hshrink.isUnlink (hrotate.isUnlink hfinal))
  simpa only [hD] using hDunlink

end BookCircleCompletion

open BookSixth

theorem solution {m : ℕ} (C : Fin m → Set Space3)
    (hround : ∀ i, RoundCircle (C i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hpairs : ∀ i j, i ≠ j → IsUnlink (![C i, C j] : Fin 2 → Set Space3)) :
    IsUnlink C :=
  BookCircleCompletion.round_circle_unlink C hround hdisjoint hpairs

#print axioms solution
