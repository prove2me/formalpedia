-- Prove2me | solution 1 for LinearOptimization.lp_optimal_cost_concave_in_cost
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T22:03:55.701487+00:00
-- url     : https://prove2.me/submissions/9c9c7992-a05e-442c-9d56-2d697d2aa769

import Mathlib.Analysis.Convex.Function
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_LinearOptimization_OptimalCostFunction
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Tactic.Linarith

open Matrix

private lemma lpCost_ne_top_of_feasible {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hfeas : (LinearOptimization.stdPolyhedron A b).Nonempty)
    (c : Fin n → ℝ) :
    LinearOptimization.lpOptimalCostCost A b c ≠ ⊤ := by
  obtain ⟨x, hx⟩ := hfeas
  intro htop
  have hle : LinearOptimization.lpOptimalCostCost A b c ≤
      ((c ⬝ᵥ x : ℝ) : EReal) := by
    rw [LinearOptimization.lpOptimalCostCost, LinearOptimization.lpValue]
    exact iInf_le_of_le x (iInf_le_of_le hx le_rfl)
  rw [htop] at hle
  exact (not_le_of_gt (EReal.coe_lt_top (c ⬝ᵥ x))) hle

private lemma finite_value_lower_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (htop : LinearOptimization.lpOptimalCostCost A b c ≠ ⊤)
    (hbot : LinearOptimization.lpOptimalCostCost A b c ≠ ⊥) :
    ∀ y ∈ LinearOptimization.stdPolyhedron A b,
      (LinearOptimization.lpOptimalCostCost A b c).toReal ≤ c ⬝ᵥ y := by
  intro y hy
  have hle : LinearOptimization.lpOptimalCostCost A b c ≤
      ((c ⬝ᵥ y : ℝ) : EReal) := by
    rw [LinearOptimization.lpOptimalCostCost, LinearOptimization.lpValue]
    exact iInf_le_of_le y (iInf_le_of_le hy le_rfl)
  rw [← EReal.coe_toReal htop hbot] at hle
  exact EReal.coe_le_coe_iff.mp hle

private lemma finiteCostSet_convex {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hfeas : (LinearOptimization.stdPolyhedron A b).Nonempty) :
    Convex ℝ (LinearOptimization.finiteCostSet A b) := by
  classical
  intro c₁ hc₁ c₂ hc₂ a d ha hd had
  constructor
  · exact lpCost_ne_top_of_feasible A b hfeas _
  · intro hbot
    let v₁ := (LinearOptimization.lpOptimalCostCost A b c₁).toReal
    let v₂ := (LinearOptimization.lpOptimalCostCost A b c₂).toReal
    have hlower : (((a * v₁ + d * v₂ : ℝ)) : EReal) ≤
        LinearOptimization.lpOptimalCostCost A b (a • c₁ + d • c₂) := by
      rw [LinearOptimization.lpOptimalCostCost, LinearOptimization.lpValue]
      apply le_iInf
      intro y
      apply le_iInf
      intro hy
      apply EReal.coe_le_coe_iff.mpr
      have h₁ := finite_value_lower_bound A b c₁ hc₁.1 hc₁.2 y hy
      have h₂ := finite_value_lower_bound A b c₂ hc₂.1 hc₂.2 y hy
      change a * v₁ + d * v₂ ≤ (a • c₁ + d • c₂) ⬝ᵥ y
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
        smul_eq_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ ha)
        (mul_le_mul_of_nonneg_left h₂ hd)
    rw [hbot] at hlower
    exact (not_le_of_gt (EReal.bot_lt_coe (a * v₁ + d * v₂))) hlower

private lemma feasible_step_of_tangent {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (xstar d : Fin n → ℝ)
    (hx : xstar ∈ LinearOptimization.stdPolyhedron A b)
    (hAd : A.mulVec d = 0)
    (hsign : ∀ j, xstar j = 0 → 0 ≤ d j) :
    ∃ t > (0 : ℝ), xstar + t • d ∈ LinearOptimization.stdPolyhedron A b := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun j ↦ d j < 0)
  by_cases hs : s.Nonempty
  · obtain ⟨j₀, hj₀s, hj₀min⟩ := Finset.exists_min_image s
      (fun j ↦ xstar j / (-d j)) hs
    have hdj₀ : d j₀ < 0 := (Finset.mem_filter.mp hj₀s).2
    have hxj₀ : 0 < xstar j₀ := by
      have hxnonneg := hx.2 j₀
      have hxne : xstar j₀ ≠ 0 := by
        intro hz
        exact (not_lt_of_ge (hsign j₀ hz)) hdj₀
      exact lt_of_le_of_ne hxnonneg (Ne.symm hxne)
    let t : ℝ := (xstar j₀ / (-d j₀)) / 2
    have ht : 0 < t := by
      dsimp [t]
      have hden₀ : 0 < -d j₀ := by linarith
      have : 0 < xstar j₀ / (-d j₀) := div_pos hxj₀ hden₀
      linarith
    refine ⟨t, ht, ?_⟩
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx.1, hAd, smul_zero,
        add_zero]
    · intro j
      by_cases hdj : d j < 0
      · have hjs : j ∈ s := by simp [s, hdj]
        have hratio := hj₀min j hjs
        have hden : 0 < -d j := by linarith
        have ht_le_ratio : t ≤ xstar j / (-d j) := by
          dsimp [t]
          have hden₀ : 0 < -d j₀ := by linarith
          have hratio₀ : 0 < xstar j₀ / (-d j₀) := div_pos hxj₀ hden₀
          linarith
        have hmul : t * (-d j) ≤ xstar j :=
          (le_div_iff₀ hden).mp ht_le_ratio
        change 0 ≤ xstar j + t * d j
        linarith
      · have hdnonneg : 0 ≤ d j := le_of_not_gt hdj
        change 0 ≤ xstar j + t * d j
        exact add_nonneg (hx.2 j) (mul_nonneg (le_of_lt ht) hdnonneg)
  · refine ⟨1, by norm_num, ?_⟩
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx.1, hAd, smul_zero,
        add_zero]
    · intro j
      have hdj : 0 ≤ d j := by
        by_contra hneg
        have : j ∈ s := by simp [s, lt_of_not_ge hneg]
        exact hs ⟨j, this⟩
      change 0 ≤ xstar j + 1 * d j
      simpa using add_nonneg (hx.2 j) hdj

private lemma unique_optimal_uniform_tangent {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c xstar : Fin n → ℝ)
    (hopt : LinearOptimization.IsLpOptimal c
      (LinearOptimization.stdPolyhedron A b) xstar)
    (huniq : ∀ y, LinearOptimization.IsLpOptimal c
      (LinearOptimization.stdPolyhedron A b) y → y = xstar) :
    ∃ δ > (0 : ℝ), ∀ d : Fin n → ℝ,
      A.mulVec d = 0 → (∀ j, xstar j = 0 → 0 ≤ d j) →
      ‖d‖ = 1 → δ ≤ c ⬝ᵥ d := by
  classical
  let D : Set (Fin n → ℝ) :=
    {d | A.mulVec d = 0 ∧ ∀ j, xstar j = 0 → 0 ≤ d j}
  let Z : Set (Fin n → ℝ) :=
    ⋂ j, ⋂ (_h : xstar j = 0), {d | 0 ≤ d j}
  have hkerClosed : IsClosed {d : Fin n → ℝ | A.mulVec d = 0} := by
    exact isClosed_eq (continuous_const.matrix_mulVec continuous_id) continuous_const
  have hZClosed : IsClosed Z := by
    dsimp [Z]
    exact isClosed_iInter fun j ↦ isClosed_iInter fun _ ↦
      isClosed_le continuous_const (continuous_apply j)
  have hDClosed : IsClosed D := by
    have hEq : D = {d : Fin n → ℝ | A.mulVec d = 0} ∩ Z := by
      ext d
      simp [D, Z]
    rw [hEq]
    exact hkerClosed.inter hZClosed
  let K : Set (Fin n → ℝ) := Metric.sphere 0 1 ∩ D
  have hKcompact : IsCompact K := by
    exact (isCompact_sphere (0 : Fin n → ℝ) 1).inter_right hDClosed
  by_cases hKne : K.Nonempty
  · have hcostContinuous : Continuous (fun d : Fin n → ℝ ↦ c ⬝ᵥ d) := by
      exact continuous_finset_sum Finset.univ fun j _ ↦
        continuous_const.mul (continuous_apply j)
    obtain ⟨d₀, hd₀K, hd₀min⟩ :=
      hKcompact.exists_isMinOn hKne hcostContinuous.continuousOn
    have hpositive : ∀ d ∈ K, 0 < c ⬝ᵥ d := by
      intro d hdK
      have hnorm : ‖d‖ = 1 := by
        simpa [K, Metric.mem_sphere, dist_eq_norm] using hdK.1
      have hdne : d ≠ 0 := by
        intro hz
        rw [hz, norm_zero] at hnorm
        norm_num at hnorm
      obtain ⟨t, ht, hstep⟩ := feasible_step_of_tangent A b xstar d hopt.1
        hdK.2.1 hdK.2.2
      have hle := hopt.2 (xstar + t • d) hstep
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at hle
      have hnonneg : 0 ≤ c ⬝ᵥ d := by nlinarith
      have hnecost : c ⬝ᵥ d ≠ 0 := by
        intro hzero
        have hstepOpt : LinearOptimization.IsLpOptimal c
            (LinearOptimization.stdPolyhedron A b) (xstar + t • d) := by
          refine ⟨hstep, ?_⟩
          intro y hy
          have hycost := hopt.2 y hy
          rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hzero, mul_zero,
            add_zero]
          exact hycost
        have heq := huniq (xstar + t • d) hstepOpt
        have htd : t • d = 0 := by simpa using sub_eq_zero.mpr heq
        exact hdne (smul_eq_zero.mp htd |>.resolve_left (ne_of_gt ht))
      exact lt_of_le_of_ne hnonneg (Ne.symm hnecost)
    refine ⟨c ⬝ᵥ d₀, hpositive d₀ hd₀K, ?_⟩
    intro d hAd hsign hnorm
    apply hd₀min
    exact ⟨by simpa [Metric.mem_sphere, dist_eq_norm] using hnorm, hAd, hsign⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro d hAd hsign hnorm
    exfalso
    apply hKne
    exact ⟨d, by
      exact ⟨by simpa [K, Metric.mem_sphere, dist_eq_norm] using hnorm,
        hAd, hsign⟩⟩

private lemma unique_optimal_stable_cost {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c xstar : Fin n → ℝ)
    (hopt : LinearOptimization.IsLpOptimal c
      (LinearOptimization.stdPolyhedron A b) xstar)
    (huniq : ∀ y, LinearOptimization.IsLpOptimal c
      (LinearOptimization.stdPolyhedron A b) y → y = xstar) :
    ∃ ε > (0 : ℝ), ∀ c' : Fin n → ℝ, (∀ j, |c' j - c j| < ε) →
      LinearOptimization.IsLpOptimal c'
        (LinearOptimization.stdPolyhedron A b) xstar := by
  classical
  obtain ⟨δ, hδ, hmargin⟩ := unique_optimal_uniform_tangent A b c xstar hopt huniq
  let ε : ℝ := δ / (n + 1)
  have hden : (0 : ℝ) < n + 1 := by positivity
  have hε : 0 < ε := div_pos hδ hden
  refine ⟨ε, hε, ?_⟩
  intro c' hc'
  refine ⟨hopt.1, ?_⟩
  intro y hy
  by_cases hyx : y = xstar
  · subst y
    exact le_rfl
  · let d : Fin n → ℝ := y - xstar
    have hdne : d ≠ 0 := by
      intro hd
      apply hyx
      exact sub_eq_zero.mp hd
    have hnormpos : 0 < ‖d‖ := norm_pos_iff.mpr hdne
    have hAd : A.mulVec d = 0 := by
      dsimp [d]
      rw [Matrix.mulVec_sub, hy.1, hopt.1.1, sub_self]
    have hsign : ∀ j, xstar j = 0 → 0 ≤ d j := by
      intro j hxj
      dsimp [d]
      simp only [Pi.sub_apply, hxj, sub_zero]
      exact hy.2 j
    let u : Fin n → ℝ := (‖d‖)⁻¹ • d
    have huAd : A.mulVec u = 0 := by
      dsimp [u]
      rw [Matrix.mulVec_smul, hAd, smul_zero]
    have husign : ∀ j, xstar j = 0 → 0 ≤ u j := by
      intro j hxj
      change 0 ≤ ‖d‖⁻¹ * d j
      exact mul_nonneg (inv_nonneg.mpr (le_of_lt hnormpos)) (hsign j hxj)
    have hunorm : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm,
        inv_mul_cancel₀ (ne_of_gt hnormpos)]
    have hunitmargin := hmargin u huAd husign hunorm
    have hcd : δ * ‖d‖ ≤ c ⬝ᵥ d := by
      change δ ≤ c ⬝ᵥ ((‖d‖)⁻¹ • d) at hunitmargin
      rw [dotProduct_smul, smul_eq_mul] at hunitmargin
      have hmul := mul_le_mul_of_nonneg_right hunitmargin (le_of_lt hnormpos)
      field_simp [ne_of_gt hnormpos] at hmul
      exact hmul
    have hnpos : 0 < n := by
      by_contra hn
      have hn0 : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      exact hdne (Subsingleton.elim d 0)
    have herror : |(c' - c) ⬝ᵥ d| < δ * ‖d‖ := by
      have hterm : ∀ j : Fin n, |(c' j - c j) * d j| < ε * ‖d‖ := by
        intro j
        have hcoord : |d j| ≤ ‖d‖ := by
          have hj := (pi_norm_le_iff_of_nonneg (norm_nonneg d)).mp le_rfl j
          simpa [Real.norm_eq_abs] using hj
        rw [abs_mul]
        calc
          |c' j - c j| * |d j| ≤ |c' j - c j| * ‖d‖ :=
            mul_le_mul_of_nonneg_left hcoord (abs_nonneg _)
          _ < ε * ‖d‖ := mul_lt_mul_of_pos_right (hc' j) hnormpos
      calc
        |(c' - c) ⬝ᵥ d| ≤ ∑ j : Fin n, |(c' j - c j) * d j| := by
          simpa [dotProduct] using Finset.abs_sum_le_sum_abs
            (fun j : Fin n ↦ (c' j - c j) * d j) Finset.univ
        _ < ∑ _j : Fin n, ε * ‖d‖ :=
          Finset.sum_lt_sum_of_nonempty
            ⟨⟨0, hnpos⟩, Finset.mem_univ _⟩
            (fun j _ ↦ hterm j)
        _ = n * (ε * ‖d‖) := by simp [nsmul_eq_mul]
        _ < δ * ‖d‖ := by
          dsimp [ε]
          have hnlt : (n : ℝ) < n + 1 := by norm_num
          have : (n : ℝ) * (δ / (n + 1)) < δ := by
            calc
              (n : ℝ) * (δ / (n + 1)) = δ * ((n : ℝ) / (n + 1)) := by ring
              _ < δ * 1 := mul_lt_mul_of_pos_left (div_lt_one hden |>.mpr hnlt) hδ
              _ = δ := mul_one _
          nlinarith
    have hc'dpos : 0 < c' ⬝ᵥ d := by
      have herrlower := (abs_lt.mp herror).1
      have hc'eq : c' ⬝ᵥ d = c ⬝ᵥ d + (c' - c) ⬝ᵥ d := by
        rw [← add_dotProduct]
        congr 1
        abel
      rw [hc'eq]
      nlinarith
    dsimp [d] at hc'dpos
    rw [dotProduct_sub] at hc'dpos
    linarith

private lemma lpCost_eq_of_optimal {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c x : Fin n → ℝ)
    (hopt : LinearOptimization.IsLpOptimal c
      (LinearOptimization.stdPolyhedron A b) x) :
    LinearOptimization.lpOptimalCostCost A b c = ((c ⬝ᵥ x : ℝ) : EReal) := by
  apply le_antisymm
  · rw [LinearOptimization.lpOptimalCostCost, LinearOptimization.lpValue]
    exact iInf_le_of_le x (iInf_le_of_le hopt.1 le_rfl)
  · rw [LinearOptimization.lpOptimalCostCost, LinearOptimization.lpValue]
    apply le_iInf
    intro y
    apply le_iInf
    intro hy
    exact EReal.coe_le_coe_iff.mpr (hopt.2 y hy)

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (G : (Fin n → ℝ) → ℝ)
    (hrank : LinearIndependent ℝ (fun i => A i))
    (hfeas : (LinearOptimization.stdPolyhedron A b).Nonempty)
    (hG : ∀ c ∈ LinearOptimization.finiteCostSet A b,
      ((G c : ℝ) : EReal) = LinearOptimization.lpOptimalCostCost A b c) :
    Convex ℝ (LinearOptimization.finiteCostSet A b) ∧
    ConcaveOn ℝ (LinearOptimization.finiteCostSet A b) G ∧
    ∀ (c xstar : Fin n → ℝ),
      LinearOptimization.IsLpOptimal c (LinearOptimization.stdPolyhedron A b) xstar →
      (∀ y, LinearOptimization.IsLpOptimal c
        (LinearOptimization.stdPolyhedron A b) y → y = xstar) →
      ∃ ε > (0 : ℝ), ∀ c' : Fin n → ℝ, (∀ j, |c' j - c j| < ε) →
        c' ∈ LinearOptimization.finiteCostSet A b ∧
          G c' = G c + (c' - c) ⬝ᵥ xstar := by
  classical
  have hconv := finiteCostSet_convex A b hfeas
  refine ⟨hconv, ?_, ?_⟩
  · refine ⟨hconv, ?_⟩
    intro c₁ hc₁ c₂ hc₂ a d ha hd had
    have hccomb := hconv hc₁ hc₂ ha hd had
    have hlower : (((a * G c₁ + d * G c₂ : ℝ)) : EReal) ≤
        LinearOptimization.lpOptimalCostCost A b (a • c₁ + d • c₂) := by
      rw [LinearOptimization.lpOptimalCostCost, LinearOptimization.lpValue]
      apply le_iInf
      intro y
      apply le_iInf
      intro hy
      apply EReal.coe_le_coe_iff.mpr
      have h₁ : G c₁ ≤ c₁ ⬝ᵥ y := by
        have hv := finite_value_lower_bound A b c₁ hc₁.1 hc₁.2 y hy
        have heq := hG c₁ hc₁
        rw [← EReal.coe_toReal hc₁.1 hc₁.2] at heq
        have := EReal.coe_eq_coe_iff.mp heq
        linarith
      have h₂ : G c₂ ≤ c₂ ⬝ᵥ y := by
        have hv := finite_value_lower_bound A b c₂ hc₂.1 hc₂.2 y hy
        have heq := hG c₂ hc₂
        rw [← EReal.coe_toReal hc₂.1 hc₂.2] at heq
        have := EReal.coe_eq_coe_iff.mp heq
        linarith
      change a * G c₁ + d * G c₂ ≤ (a • c₁ + d • c₂) ⬝ᵥ y
      rw [add_dotProduct, smul_dotProduct, smul_dotProduct, smul_eq_mul,
        smul_eq_mul]
      exact add_le_add (mul_le_mul_of_nonneg_left h₁ ha)
        (mul_le_mul_of_nonneg_left h₂ hd)
    rw [← hG _ hccomb] at hlower
    exact EReal.coe_le_coe_iff.mp hlower
  · intro c xstar hopt huniq
    obtain ⟨ε, hε, hstable⟩ := unique_optimal_stable_cost A b c xstar hopt huniq
    refine ⟨ε, hε, ?_⟩
    intro c' hc'
    have hopt' := hstable c' hc'
    have hval := lpCost_eq_of_optimal A b c' xstar hopt'
    have hc'mem : c' ∈ LinearOptimization.finiteCostSet A b := by
      constructor
      · rw [hval]
        exact EReal.coe_ne_top _
      · rw [hval]
        exact EReal.coe_ne_bot _
    have hvalc := lpCost_eq_of_optimal A b c xstar hopt
    have hcmem : c ∈ LinearOptimization.finiteCostSet A b := by
      constructor
      · rw [hvalc]
        exact EReal.coe_ne_top _
      · rw [hvalc]
        exact EReal.coe_ne_bot _
    refine ⟨hc'mem, ?_⟩
    have hGc' : G c' = c' ⬝ᵥ xstar := by
      have heq := hG c' hc'mem
      rw [hval] at heq
      exact EReal.coe_eq_coe_iff.mp heq
    have hGc : G c = c ⬝ᵥ xstar := by
      have heq := hG c hcmem
      rw [hvalc] at heq
      exact EReal.coe_eq_coe_iff.mp heq
    rw [hGc', hGc, sub_dotProduct]
    ring
