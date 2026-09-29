-- Prove2me | solution 1 for ConvexOptimization.conic_slater_strong_duality
-- status  : ACCEPTED   (prove)
-- author  : @jianglsbz
-- created : 2026-08-15T05:20:29.512729+00:00
-- url     : https://prove2.me/submissions/53978b54-35c2-4e27-8ba3-d243fec69be9

import Mathlib
import Definitions.Def_dualCone
import Theorems.Thm_ConvexOptimization_zero_mem_of_closed_pos_cone
import Theorems.Thm_ConvexOptimization_add_mem_of_convex_cone
import Theorems.Thm_ConvexOptimization_smul_mem_dualCone
import Theorems.Thm_ConvexOptimization_dualCone_inner_pos_of_mem_interior

open scoped RealInnerProductSpace ENNReal
open MeasureTheory

namespace ConicSlaterAux

open ConvexOptimization

/-- A strict convex combination of two strict inequalities. -/
theorem strict_combo {t₁ t₂ p₁ p₂ q₁ q₂ : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂)
    (hsum : t₁ + t₂ = 1) (h₁ : p₁ < q₁) (h₂ : p₂ < q₂) :
    t₁ * p₁ + t₂ * p₂ < t₁ * q₁ + t₂ * q₂ := by
  rcases eq_or_lt_of_le ht₁ with h | h
  · have ht2 : t₂ = 1 := by linarith
    rw [← h, ht2]; simpa using h₂
  · linarith [mul_lt_mul_of_pos_left h₁ h, mul_le_mul_of_nonneg_left h₂.le ht₂]

/-- For a convex cone `K`, the interior absorbs the cone: `interior K + K ⊆ interior K`. -/
theorem interior_add_mem {d : ℕ} {K : Set (EuclideanSpace ℝ (Fin d))} (hKconv : Convex ℝ K)
    (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K) {w k : EuclideanSpace ℝ (Fin d)}
    (hw : w ∈ interior K) (hk : k ∈ K) : w + k ∈ interior K := by
  have hsub : (fun y => y + k) '' interior K ⊆ K := by
    rintro _ ⟨y, hy, rfl⟩
    exact ConvexOptimization.add_mem_of_convex_cone K hKconv hKcone y k (interior_subset hy) hk
  have hopen : IsOpen ((fun y => y + k) '' interior K) := by
    have := (Homeomorph.addRight k).isOpenMap (interior K) isOpen_interior
    simpa using this
  exact interior_maximal hsub hopen ⟨w, hw, rfl⟩

/-! ### Stage A: strong duality for the cone constraint alone -/

/-- **Stage A.** Over any convex set `M` of "already feasible" points, a Slater point for the
generalized inequality `f x ≼_K 0` produces a dual multiplier `z ∈ K*` whose Lagrangian
dominates the optimal value `P` on all of `M`. -/
theorem stageA {n d : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKconv : Convex ℝ K) (hKclosed : IsClosed K)
    (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (hf : ∀ x y : EuclideanSpace ℝ (Fin n), ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      θ • f x + (1 - θ) • f y - f (θ • x + (1 - θ) • y) ∈ K)
    (M : Set (EuclideanSpace ℝ (Fin n))) (hM : Convex ℝ M)
    (xs : EuclideanSpace ℝ (Fin n)) (hxsM : xs ∈ M) (hxs : -f xs ∈ interior K)
    (P : ℝ) (hP : ∀ x ∈ M, -f x ∈ K → P ≤ f₀ x) :
    ∃ z ∈ dualCone K, ∀ x ∈ M, P ≤ f₀ x + ⟪z, f x⟫ := by
  classical
  have hKne : K.Nonempty := ⟨-f xs, interior_subset hxs⟩
  have h0K : (0 : EuclideanSpace ℝ (Fin d)) ∈ K :=
    ConvexOptimization.zero_mem_of_closed_pos_cone K hKclosed hKcone hKne
  -- The "achievable pairs" set and the "better than optimal" ray.
  set A : Set (EuclideanSpace ℝ (Fin d) × ℝ) :=
    {q | ∃ x ∈ M, q.1 - f x ∈ K ∧ f₀ x ≤ q.2} with hAdef
  set B : Set (EuclideanSpace ℝ (Fin d) × ℝ) := {q | q.1 = 0 ∧ q.2 < P} with hBdef
  have hmemA : ∀ q : EuclideanSpace ℝ (Fin d) × ℝ,
      q ∈ A ↔ ∃ x ∈ M, q.1 - f x ∈ K ∧ f₀ x ≤ q.2 := by
    intro q; rw [hAdef]; rfl
  have hmemB : ∀ q : EuclideanSpace ℝ (Fin d) × ℝ, q ∈ B ↔ q.1 = 0 ∧ q.2 < P := by
    intro q; rw [hBdef]; rfl
  -- `A` is convex.
  have hAconv : Convex ℝ A := by
    rintro ⟨u₁, t₁⟩ h₁ ⟨u₂, t₂⟩ h₂ θ₁ θ₂ hθ₁ hθ₂ hsum
    obtain ⟨x₁, hx₁, hk₁, hl₁⟩ := (hmemA _).1 h₁
    obtain ⟨x₂, hx₂, hk₂, hl₂⟩ := (hmemA _).1 h₂
    dsimp only at hk₁ hl₁ hk₂ hl₂
    have hθ₂' : θ₂ = 1 - θ₁ := by linarith
    subst hθ₂'
    rw [hmemA]
    refine ⟨θ₁ • x₁ + (1 - θ₁) • x₂, hM hx₁ hx₂ hθ₁ hθ₂ hsum, ?_, ?_⟩
    · have hcomb : θ₁ • (u₁ - f x₁) + (1 - θ₁) • (u₂ - f x₂) ∈ K :=
        hKconv hk₁ hk₂ hθ₁ hθ₂ hsum
      have hcv := hf x₁ x₂ θ₁ hθ₁ (by linarith)
      have hEq : (θ₁ • u₁ + (1 - θ₁) • u₂) - f (θ₁ • x₁ + (1 - θ₁) • x₂) =
          (θ₁ • (u₁ - f x₁) + (1 - θ₁) • (u₂ - f x₂)) +
            (θ₁ • f x₁ + (1 - θ₁) • f x₂ - f (θ₁ • x₁ + (1 - θ₁) • x₂)) := by module
      show (θ₁ • u₁ + (1 - θ₁) • u₂) - f (θ₁ • x₁ + (1 - θ₁) • x₂) ∈ K
      rw [hEq]
      exact ConvexOptimization.add_mem_of_convex_cone K hKconv hKcone _ _ hcomb hcv
    · show f₀ (θ₁ • x₁ + (1 - θ₁) • x₂) ≤ θ₁ * t₁ + (1 - θ₁) * t₂
      have hjensen := hf₀.2 (Set.mem_univ x₁) (Set.mem_univ x₂) hθ₁ hθ₂ hsum
      simp only [smul_eq_mul] at hjensen
      have e₁ := mul_le_mul_of_nonneg_left hl₁ hθ₁
      have e₂ := mul_le_mul_of_nonneg_left hl₂ hθ₂
      linarith
  -- `B` is convex.
  have hBconv : Convex ℝ B := by
    rintro ⟨u₁, t₁⟩ h₁ ⟨u₂, t₂⟩ h₂ θ₁ θ₂ hθ₁ hθ₂ hsum
    obtain ⟨hu₁, ht₁⟩ := (hmemB _).1 h₁
    obtain ⟨hu₂, ht₂⟩ := (hmemB _).1 h₂
    dsimp only at hu₁ ht₁ hu₂ ht₂
    rw [hmemB]
    refine ⟨?_, ?_⟩
    · show θ₁ • u₁ + θ₂ • u₂ = 0
      rw [hu₁, hu₂]; simp
    · show θ₁ * t₁ + θ₂ * t₂ < P
      have hcomb := strict_combo hθ₁ hθ₂ hsum ht₁ ht₂
      have hPP : θ₁ * P + θ₂ * P = P := by rw [← add_mul, hsum, one_mul]
      linarith
  -- `A` has nonempty interior, thanks to the Slater point.
  have hAint : ((0 : EuclideanSpace ℝ (Fin d)), f₀ xs + 1) ∈ interior A := by
    have hsub : {q : EuclideanSpace ℝ (Fin d) × ℝ | q.1 - f xs ∈ interior K ∧ f₀ xs < q.2} ⊆ A := by
      rintro ⟨u, t⟩ ⟨hu, ht⟩
      rw [hmemA]
      exact ⟨xs, hxsM, interior_subset hu, ht.le⟩
    have hopen : IsOpen {q : EuclideanSpace ℝ (Fin d) × ℝ |
        q.1 - f xs ∈ interior K ∧ f₀ xs < q.2} := by
      refine IsOpen.inter ?_ ?_
      · exact isOpen_interior.preimage (continuous_fst.sub continuous_const)
      · exact isOpen_lt continuous_const continuous_snd
    refine interior_maximal hsub hopen ⟨?_, by linarith⟩
    show (0 : EuclideanSpace ℝ (Fin d)) - f xs ∈ interior K
    simpa using hxs
  -- The two sets are separated.
  have hdisj : Disjoint (interior A) B := by
    rw [Set.disjoint_left]
    rintro ⟨u, t⟩ hq hB
    obtain ⟨hu, ht⟩ := (hmemB _).1 hB
    obtain ⟨x, hxM, hk, hle⟩ := (hmemA _).1 (interior_subset hq)
    simp only at hu
    rw [hu] at hk
    have := hP x hxM (by simpa using hk)
    linarith
  obtain ⟨Φ, c, hΦne, hΦA, hΦB⟩ :=
    geometric_hahn_banach_of_nonempty_interior hAconv hBconv hdisj ⟨_, hAint⟩
      ⟨((0 : EuclideanSpace ℝ (Fin d)), P - 1), (hmemB _).2 ⟨rfl, by linarith⟩⟩
  -- Decompose the separating functional.
  set μ : ℝ := Φ (0, 1) with hμdef
  set L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ :=
    Φ.comp (ContinuousLinearMap.inl ℝ (EuclideanSpace ℝ (Fin d)) ℝ) with hLdef
  set z₀ : EuclideanSpace ℝ (Fin d) := (InnerProductSpace.toDual ℝ _).symm L with hz₀def
  have hz₀ : ∀ u, ⟪z₀, u⟫ = Φ (u, 0) := by
    intro u
    rw [hz₀def, InnerProductSpace.toDual_symm_apply]
    rfl
  have hdec : ∀ (u : EuclideanSpace ℝ (Fin d)) (t : ℝ), Φ (u, t) = ⟪z₀, u⟫ + t * μ := by
    intro u t
    have hsplit : ((u, t) : EuclideanSpace ℝ (Fin d) × ℝ)
        = (u, 0) + t • ((0 : EuclideanSpace ℝ (Fin d)), (1 : ℝ)) := by
      simp [Prod.ext_iff]
    rw [hsplit, map_add, map_smul, hz₀ u, smul_eq_mul, hμdef]
  -- The `t`-coefficient is nonpositive.
  have hμle : μ ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    set s : ℝ := min (P - 1) ((c - 1) / μ) with hsdef
    have hs1 : s < P := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hs2 : s * μ ≤ c - 1 := by
      have hle : s ≤ (c - 1) / μ := min_le_right _ _
      have := mul_le_mul_of_nonneg_right hle hcon.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hcon)] at this
    have hb := hΦB ((0 : EuclideanSpace ℝ (Fin d)), s) ((hmemB _).2 ⟨rfl, hs1⟩)
    rw [hdec, inner_zero_right, zero_add] at hb
    linarith
  -- Hence the separating constant is below `P * μ`.
  have hcP : c ≤ P * μ := by
    have htend : Filter.Tendsto (fun s : ℝ => s * μ) (nhdsWithin P (Set.Iio P)) (nhds (P * μ)) :=
      ((continuous_id.mul continuous_const).tendsto P).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto htend ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hb := hΦB ((0 : EuclideanSpace ℝ (Fin d)), s) ((hmemB _).2 ⟨rfl, hs⟩)
    rwa [hdec, inner_zero_right, zero_add] at hb
  -- `-z₀` lies in the dual cone.
  have hz₀K : ∀ k ∈ K, ⟪z₀, k⟫ ≤ 0 := by
    intro k hk
    by_contra hcon
    push_neg at hcon
    set C₀ : ℝ := ⟪z₀, f xs⟫ + f₀ xs * μ with hC₀def
    set lam : ℝ := (|c - C₀| + 1) / ⟪z₀, k⟫ with hlamdef
    have hlampos : 0 < lam := by
      rw [hlamdef]; positivity
    have hmem : ((f xs + lam • k, f₀ xs) : EuclideanSpace ℝ (Fin d) × ℝ) ∈ A := by
      rw [hmemA]
      refine ⟨xs, hxsM, ?_, le_rfl⟩
      show (f xs + lam • k) - f xs ∈ K
      have hsimp : (f xs + lam • k) - f xs = lam • k := by abel
      rw [hsimp]
      exact hKcone lam hlampos k hk
    have hb := hΦA _ hmem
    rw [hdec, inner_add_right, real_inner_smul_right] at hb
    have hprod : lam * ⟪z₀, k⟫ = |c - C₀| + 1 := by
      rw [hlamdef, div_mul_cancel₀ _ (ne_of_gt hcon)]
    rw [hprod] at hb
    have habs : c - C₀ ≤ |c - C₀| := le_abs_self _
    rw [hC₀def] at hb
    linarith
  -- The main domination inequality.
  have hmain : ∀ x ∈ M, ⟪z₀, f x⟫ + f₀ x * μ ≤ P * μ := by
    intro x hx
    have hmem : ((f x, f₀ x) : EuclideanSpace ℝ (Fin d) × ℝ) ∈ A := by
      rw [hmemA]
      refine ⟨x, hx, ?_, le_rfl⟩
      show f x - f x ∈ K
      simpa using h0K
    have hb := hΦA _ hmem
    rw [hdec] at hb
    linarith
  -- The `t`-coefficient is in fact strictly negative (this is where Slater is used).
  have hμlt : μ < 0 := by
    rcases lt_or_eq_of_le hμle with hlt | heq
    · exact hlt
    exfalso
    have hzz : z₀ = 0 := by
      by_contra hne
      have hz'dual : -z₀ ∈ dualCone K := by
        intro k hk
        rw [inner_neg_right]
        have h1 := hz₀K k hk
        rw [real_inner_comm] at h1
        linarith
      have hne' : -z₀ ≠ 0 := by simpa using hne
      have hpos :=
        ConvexOptimization.dualCone_inner_pos_of_mem_interior K (-z₀) (-f xs) hz'dual hne' hxs
      rw [inner_neg_neg, real_inner_comm] at hpos
      have hm := hmain xs hxsM
      rw [heq] at hm
      simp only [mul_zero, add_zero] at hm
      linarith
    apply hΦne
    refine ContinuousLinearMap.ext fun q => ?_
    obtain ⟨u, t⟩ := q
    rw [hdec, hzz, heq]
    simp
  -- Rescale to get the multiplier.
  refine ⟨(1 / μ) • z₀, ?_, ?_⟩
  · intro k hk
    rw [real_inner_smul_right]
    have h1 : ⟪z₀, k⟫ ≤ 0 := hz₀K k hk
    have h2 : ⟪k, z₀⟫ ≤ 0 := by rwa [real_inner_comm] at h1
    have h3 : 1 / μ < 0 := div_neg_of_pos_of_neg one_pos hμlt
    nlinarith
  · intro x hx
    have hm := hmain x hx
    rw [real_inner_smul_left]
    have hμne : μ ≠ 0 := ne_of_lt hμlt
    have key : (f₀ x + 1 / μ * ⟪z₀, f x⟫) * μ ≤ P * μ := by
      have hexp : (f₀ x + 1 / μ * ⟪z₀, f x⟫) * μ = f₀ x * μ + ⟪z₀, f x⟫ := by
        field_simp
      rw [hexp]; linarith
    exact (mul_le_mul_right_of_neg hμlt).mp key

/-! ### Stage B: eliminating the affine equality constraints -/

/-- A linearly independent family of vectors gives a *surjective* linear map
`x ↦ (⟪a j, x⟫)ⱼ`, and moreover a continuous linear right inverse. -/
theorem exists_right_inverse {n p : ℕ} (a : Fin p → EuclideanSpace ℝ (Fin n))
    (ha : LinearIndependent ℝ a) :
    ∃ R : (Fin p → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n),
      Continuous R ∧ ∀ (v : Fin p → ℝ) (j : Fin p), ⟪a j, R v⟫ = v j := by
  classical
  set T : (Fin p → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) := Fintype.linearCombination ℝ a with hTdef
  have hTapp : ∀ c : Fin p → ℝ, T c = ∑ i, c i • a i := by
    intro c; rw [hTdef]; exact Fintype.linearCombination_apply (R := ℝ) a c
  set G : (Fin p → ℝ) →ₗ[ℝ] (Fin p → ℝ) :=
    LinearMap.pi (fun j => (innerSL ℝ (a j)).toLinearMap ∘ₗ T) with hGdef
  have hGapp : ∀ (c : Fin p → ℝ) (j : Fin p), G c j = ⟪a j, T c⟫ := by
    intro c j; rw [hGdef]; rfl
  have hGinj : Function.Injective G := by
    rw [injective_iff_map_eq_zero]
    intro c hc
    have hj : ∀ j, ⟪a j, T c⟫ = 0 := by
      intro j
      have := congrFun hc j
      rwa [hGapp] at this
    have hsq : ⟪T c, T c⟫ = 0 := by
      calc ⟪T c, T c⟫ = ∑ i, c i * ⟪a i, T c⟫ := by
            conv_lhs => rw [hTapp c]
            rw [sum_inner]
            exact Finset.sum_congr rfl fun i _ => real_inner_smul_left _ _ _
        _ = 0 := by simp [hj]
    have hT0 : T c = 0 := by
      simpa using inner_self_eq_zero.mp hsq
    funext i
    exact Fintype.linearIndependent_iff.mp ha c (by rw [← hTapp c]; exact hT0) i
  have hGsurj : Function.Surjective G := LinearMap.injective_iff_surjective.mp hGinj
  set Ge : (Fin p → ℝ) ≃ₗ[ℝ] (Fin p → ℝ) := LinearEquiv.ofBijective G ⟨hGinj, hGsurj⟩ with hGedef
  refine ⟨T ∘ₗ (Ge.symm : (Fin p → ℝ) →ₗ[ℝ] (Fin p → ℝ)), ?_, ?_⟩
  · exact LinearMap.continuous_of_finiteDimensional _
  · intro v j
    have hGv : G (Ge.symm v) = v := by
      have h := Ge.apply_symm_apply v
      rwa [hGedef, LinearEquiv.ofBijective_apply] at h
    calc ⟪a j, (T ∘ₗ (Ge.symm : (Fin p → ℝ) →ₗ[ℝ] (Fin p → ℝ))) v⟫
        = G (Ge.symm v) j := (hGapp _ j).symm
      _ = v j := by rw [hGv]

/-- **Stage B.** A real-valued convex function bounded below by `P` on the affine subspace
`{x | ⟪a j, x⟫ = b j}` admits multipliers `ν` making the augmented function bounded below by `P`
everywhere. -/
theorem stageB {n p : ℕ} (g : EuclideanSpace ℝ (Fin n) → ℝ) (hg : ConvexOn ℝ Set.univ g)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a) (b : Fin p → ℝ)
    (P : ℝ) (hP : ∀ x, (∀ j, ⟪a j, x⟫ = b j) → P ≤ g x)
    (x₀ : EuclideanSpace ℝ (Fin n)) (hx₀ : ∀ j, ⟪a j, x₀⟫ = b j) :
    ∃ nu : Fin p → ℝ, ∀ x, P ≤ g x + ∑ j, nu j * (⟪a j, x⟫ - b j) := by
  classical
  have hcont : Continuous g := hg.locallyLipschitz.continuous
  obtain ⟨R, hRcont, hRapp⟩ := exists_right_inverse a ha
  -- The (open, convex) set of achievable constraint-value / objective pairs.
  set C : Set ((Fin p → ℝ) × ℝ) :=
    {q | ∃ x, (∀ j, ⟪a j, x⟫ - b j = q.1 j) ∧ g x < q.2} with hCdef
  have hmemC : ∀ q : (Fin p → ℝ) × ℝ,
      q ∈ C ↔ ∃ x, (∀ j, ⟪a j, x⟫ - b j = q.1 j) ∧ g x < q.2 := by
    intro q; rw [hCdef]; rfl
  have hCconv : Convex ℝ C := by
    rintro ⟨v₁, s₁⟩ h₁ ⟨v₂, s₂⟩ h₂ θ₁ θ₂ hθ₁ hθ₂ hsum
    obtain ⟨x₁, he₁, hl₁⟩ := (hmemC _).1 h₁
    obtain ⟨x₂, he₂, hl₂⟩ := (hmemC _).1 h₂
    dsimp only at he₁ hl₁ he₂ hl₂
    rw [hmemC]
    refine ⟨θ₁ • x₁ + θ₂ • x₂, ?_, ?_⟩
    · intro j
      show ⟪a j, θ₁ • x₁ + θ₂ • x₂⟫ - b j = θ₁ • v₁ j + θ₂ • v₂ j
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      have e₁ := he₁ j
      have e₂ := he₂ j
      simp only [smul_eq_mul]
      rw [← e₁, ← e₂]
      linear_combination (b j) * hsum
    · show g (θ₁ • x₁ + θ₂ • x₂) < θ₁ * s₁ + θ₂ * s₂
      have hjensen := hg.2 (Set.mem_univ x₁) (Set.mem_univ x₂) hθ₁ hθ₂ hsum
      simp only [smul_eq_mul] at hjensen
      have := strict_combo hθ₁ hθ₂ hsum hl₁ hl₂
      linarith
  have hCopen : IsOpen C := by
    rw [isOpen_iff_mem_nhds]
    rintro ⟨v₀, s₀⟩ hq
    obtain ⟨y, hey, hly⟩ := (hmemC _).1 hq
    dsimp only at hey hly
    have hUopen : IsOpen {q : (Fin p → ℝ) × ℝ | g (y + R (q.1 - v₀)) < q.2} := by
      refine isOpen_lt ?_ continuous_snd
      exact hcont.comp (continuous_const.add (hRcont.comp (continuous_fst.sub continuous_const)))
    have hUsub : {q : (Fin p → ℝ) × ℝ | g (y + R (q.1 - v₀)) < q.2} ⊆ C := by
      rintro ⟨v, s⟩ hs
      rw [hmemC]
      refine ⟨y + R (v - v₀), ?_, hs⟩
      intro j
      show ⟪a j, y + R (v - v₀)⟫ - b j = v j
      rw [inner_add_right, hRapp (v - v₀) j]
      have := hey j
      simp only [Pi.sub_apply]
      linarith
    refine Filter.mem_of_superset (hUopen.mem_nhds ?_) hUsub
    show g (y + R (v₀ - v₀)) < s₀
    simpa using hly
  have hnotmem : ((0 : Fin p → ℝ), P) ∉ C := by
    intro hcon
    obtain ⟨x, hex, hlx⟩ := (hmemC _).1 hcon
    dsimp only at hex hlx
    have hfeas : ∀ j, ⟪a j, x⟫ = b j := by
      intro j
      have := hex j
      simp only [Pi.zero_apply] at this
      linarith
    exact absurd (hP x hfeas) (not_le.2 hlx)
  obtain ⟨Ψ, hΨ⟩ := geometric_hahn_banach_open_point hCconv hCopen hnotmem
  -- Decompose the separating functional.
  set μ : ℝ := Ψ ((0 : Fin p → ℝ), (1 : ℝ)) with hμdef
  set ν₀ : Fin p → ℝ := fun j => Ψ ((Pi.single j (1 : ℝ) : Fin p → ℝ), (0 : ℝ)) with hν₀def
  have hdec : ∀ (v : Fin p → ℝ) (s : ℝ), Ψ (v, s) = (∑ j, ν₀ j * v j) + s * μ := by
    intro v s
    have hsplit : ((v, s) : (Fin p → ℝ) × ℝ)
        = (v, 0) + s • ((0 : Fin p → ℝ), (1 : ℝ)) := by
      simp
    have hv : ((v, (0 : ℝ)) : (Fin p → ℝ) × ℝ)
        = ∑ j, v j • ((Pi.single j (1 : ℝ) : Fin p → ℝ), (0 : ℝ)) := by
      rw [Prod.ext_iff]
      constructor
      · show v = (∑ j, v j • ((Pi.single j (1 : ℝ) : Fin p → ℝ), (0 : ℝ))).1
        rw [Prod.fst_sum]
        funext i
        simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq']
      · show (0 : ℝ) = (∑ j, v j • ((Pi.single j (1 : ℝ) : Fin p → ℝ), (0 : ℝ))).2
        rw [Prod.snd_sum]
        simp
    rw [hsplit, map_add, map_smul, hv, map_sum, smul_eq_mul, ← hμdef]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, smul_eq_mul, hν₀def, mul_comm]
  -- The `s`-coefficient is strictly negative.
  have hΨ0 : Ψ ((0 : Fin p → ℝ), P) = P * μ := by
    rw [hdec]; simp
  have hμlt : μ < 0 := by
    have hmemC' : ∀ s : ℝ, g x₀ < s → ((0 : Fin p → ℝ), s) ∈ C := by
      intro s hs
      rw [hmemC]
      refine ⟨x₀, ?_, hs⟩
      intro j
      show ⟪a j, x₀⟫ - b j = (0 : Fin p → ℝ) j
      rw [hx₀ j]; simp
    have hle : μ ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      set s : ℝ := max (g x₀ + 1) (P + 1) with hsdef
      have h1 : g x₀ < s := lt_of_lt_of_le (by linarith) (le_max_left _ _)
      have h2 : P < s := lt_of_lt_of_le (by linarith) (le_max_right _ _)
      have := hΨ ((0 : Fin p → ℝ), s) (hmemC' s h1)
      rw [hdec, hΨ0] at this
      simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at this
      nlinarith
    rcases lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    exfalso
    have := hΨ ((0 : Fin p → ℝ), g x₀ + 1) (hmemC' _ (by linarith))
    rw [hdec, hΨ0, heq] at this
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, zero_add] at this
    linarith
  -- Pass to the limit `s → g x` and rescale.
  have hkey : ∀ x, (∑ j, ν₀ j * (⟪a j, x⟫ - b j)) + g x * μ ≤ P * μ := by
    intro x
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set ε : ℝ := δ / (-μ) with hεdef
    have hεpos : 0 < ε := by rw [hεdef]; exact div_pos hδ (by linarith)
    have hmem : ((fun j => ⟪a j, x⟫ - b j : Fin p → ℝ), g x + ε) ∈ C := by
      rw [hmemC]
      exact ⟨x, fun j => rfl, by linarith⟩
    have hsep := hΨ _ hmem
    rw [hdec, hΨ0] at hsep
    have hεμ : ε * (-μ) = δ := by
      rw [hεdef, div_mul_cancel₀ _ (by linarith : (-μ) ≠ 0)]
    nlinarith [hsep, hεμ]
  refine ⟨fun j => ν₀ j / μ, fun x => ?_⟩
  have hk := hkey x
  have hμne : μ ≠ 0 := ne_of_lt hμlt
  have hsum : ∑ j, (ν₀ j / μ) * (⟪a j, x⟫ - b j)
      = (∑ j, ν₀ j * (⟪a j, x⟫ - b j)) / μ := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun j _ => by field_simp
  rw [hsum]
  have key : (g x + (∑ j, ν₀ j * (⟪a j, x⟫ - b j)) / μ) * μ ≤ P * μ := by
    have hexp : (g x + (∑ j, ν₀ j * (⟪a j, x⟫ - b j)) / μ) * μ
        = g x * μ + ∑ j, ν₀ j * (⟪a j, x⟫ - b j) := by
      field_simp
    rw [hexp]; linarith
  exact (mul_le_mul_right_of_neg hμlt).mp key

end ConicSlaterAux

open ConvexOptimization in
theorem solution {n d p : ℕ}
    (f₀ : EuclideanSpace ℝ (Fin n) → ℝ) (hf₀ : ConvexOn ℝ Set.univ f₀)
    (K : Set (EuclideanSpace ℝ (Fin d))) (hKconv : Convex ℝ K)
    (hKclosed : IsClosed K) (hKcone : ∀ t : ℝ, 0 < t → ∀ y ∈ K, t • y ∈ K)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d))
    (hf : ∀ x y : EuclideanSpace ℝ (Fin n), ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
      θ • f x + (1 - θ) • f y - f (θ • x + (1 - θ) • y) ∈ K)
    (a : Fin p → EuclideanSpace ℝ (Fin n)) (ha : LinearIndependent ℝ a)
    (b : Fin p → ℝ)
    (xs : EuclideanSpace ℝ (Fin n)) (hxs_slater : -f xs ∈ interior K)
    (hxs_eq : ∀ j, ⟪a j, xs⟫ = b j)
    (hbdd : BddBelow (f₀ '' {x | -f x ∈ K ∧ ∀ j, ⟪a j, x⟫ = b j})) :
    ∃ (z : EuclideanSpace ℝ (Fin d)) (nu : Fin p → ℝ), z ∈ dualCone K ∧
      (⨅ x : EuclideanSpace ℝ (Fin n),
        ((f₀ x + ⟪z, f x⟫ + ∑ j, nu j * (⟪a j, x⟫ - b j) : ℝ) : EReal)) =
      ((sInf (f₀ '' {x | -f x ∈ K ∧ ∀ j, ⟪a j, x⟫ = b j}) : ℝ) : EReal) := by
  classical
  set S : Set (EuclideanSpace ℝ (Fin n)) := {x | -f x ∈ K ∧ ∀ j, ⟪a j, x⟫ = b j} with hSdef
  set P : ℝ := sInf (f₀ '' S) with hPdef
  have hmemS : ∀ x, x ∈ S ↔ (-f x ∈ K ∧ ∀ j, ⟪a j, x⟫ = b j) := by
    intro x; rw [hSdef]; rfl
  have hxsS : xs ∈ S := (hmemS _).2 ⟨interior_subset hxs_slater, hxs_eq⟩
  have hSne : (f₀ '' S).Nonempty := ⟨f₀ xs, ⟨xs, hxsS, rfl⟩⟩
  have hPle : ∀ x ∈ S, P ≤ f₀ x := fun x hx => csInf_le hbdd ⟨x, hx, rfl⟩
  -- The affine subspace cut out by the equality constraints is convex.
  have hMconv : Convex ℝ {x : EuclideanSpace ℝ (Fin n) | ∀ j, ⟪a j, x⟫ = b j} := by
    intro x hx y hy s t hs ht hst
    intro j
    show ⟪a j, s • x + t • y⟫ = b j
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, hx j, hy j]
    linear_combination (b j) * hst
  -- **Stage A**: the cone constraint gives a dual vector `z ∈ K*`.
  obtain ⟨z, hz, hAbound⟩ :=
    ConicSlaterAux.stageA f₀ hf₀ K hKconv hKclosed hKcone f hf
      {x : EuclideanSpace ℝ (Fin n) | ∀ j, ⟪a j, x⟫ = b j} hMconv xs hxs_eq hxs_slater P
      (fun x hxM hxK => hPle x ((hmemS _).2 ⟨hxK, hxM⟩))
  -- The partial Lagrangian is again a real-valued convex function.
  have hgconv : ConvexOn ℝ Set.univ (fun x => f₀ x + ⟪z, f x⟫) := by
    refine ⟨convex_univ, ?_⟩
    intro x _ y _ s t hs ht hst
    have hst' : t = 1 - s := by linarith
    subst hst'
    have h1 := hf₀.2 (Set.mem_univ x) (Set.mem_univ y) hs ht hst
    simp only [smul_eq_mul] at h1
    have hK := hf x y s hs (by linarith)
    have h2 : 0 ≤ ⟪s • f x + (1 - s) • f y - f (s • x + (1 - s) • y), z⟫ := hz _ hK
    rw [real_inner_comm, inner_sub_right, inner_add_right, real_inner_smul_right,
      real_inner_smul_right] at h2
    show f₀ (s • x + (1 - s) • y) + ⟪z, f (s • x + (1 - s) • y)⟫
      ≤ s • (f₀ x + ⟪z, f x⟫) + (1 - s) • (f₀ y + ⟪z, f y⟫)
    simp only [smul_eq_mul]
    nlinarith [h1, h2]
  -- **Stage B**: the equality constraints give multipliers `ν`.
  obtain ⟨nu, hbound⟩ :=
    ConicSlaterAux.stageB (fun x => f₀ x + ⟪z, f x⟫) hgconv a ha b P
      (fun x hxM => hAbound x hxM) xs hxs_eq
  refine ⟨z, nu, hz, ?_⟩
  set I : EReal := ⨅ x : EuclideanSpace ℝ (Fin n),
      ((f₀ x + ⟪z, f x⟫ + ∑ j, nu j * (⟪a j, x⟫ - b j) : ℝ) : EReal) with hIdef
  -- `P ≤ I` is exactly the Lagrangian bound.
  have hIge : ((P : ℝ) : EReal) ≤ I := by
    rw [hIdef]
    exact le_iInf fun x => by exact_mod_cast hbound x
  -- `I ≤ P` because on the feasible set the Lagrangian is at most the objective.
  have hcoe : ∀ x ∈ S, I ≤ ((f₀ x : ℝ) : EReal) := by
    intro x hx
    obtain ⟨hxK, hxM⟩ := (hmemS _).1 hx
    rw [hIdef]
    refine le_trans (iInf_le _ x) ?_
    have h1 : ⟪z, f x⟫ ≤ 0 := by
      have hneg : (0 : ℝ) ≤ ⟪-f x, z⟫ := hz _ hxK
      rw [inner_neg_left] at hneg
      have h2 : ⟪f x, z⟫ ≤ 0 := by linarith
      rwa [real_inner_comm] at h2
    have h2 : ∑ j, nu j * (⟪a j, x⟫ - b j) = 0 := by
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [hxM j]; ring
    have h3 : f₀ x + ⟪z, f x⟫ + ∑ j, nu j * (⟪a j, x⟫ - b j) ≤ f₀ x := by
      rw [h2]; linarith
    exact_mod_cast h3
  have hntop : I ≠ ⊤ := by
    intro htop
    have h := hcoe xs hxsS
    rw [htop, top_le_iff] at h
    exact EReal.coe_ne_top (f₀ xs) h
  have hnbot : I ≠ ⊥ := by
    intro hbot
    rw [hbot, le_bot_iff] at hIge
    exact EReal.coe_ne_bot P hIge
  have hr : ((I.toReal : ℝ) : EReal) = I := EReal.coe_toReal hntop hnbot
  have hle : I.toReal ≤ P := by
    rw [hPdef]
    refine le_csInf hSne ?_
    rintro y ⟨x, hx, rfl⟩
    have h := hcoe x hx
    rw [← hr] at h
    exact_mod_cast h
  refine le_antisymm ?_ hIge
  rw [← hr]
  exact_mod_cast hle
