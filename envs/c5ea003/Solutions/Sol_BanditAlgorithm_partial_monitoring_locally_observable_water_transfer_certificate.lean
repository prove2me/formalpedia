-- Prove2me | solution 1 for BanditAlgorithm.partial_monitoring_locally_observable_water_transfer_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-13T20:04:48.51995+00:00
-- url     : https://prove2.me/submissions/55225810-80b7-4325-b516-02b188861c4e

import Theorems.Thm_BanditAlgorithm_partial_monitoring_locally_observable_monotone_vector_estimator
import Theorems.Thm_BanditAlgorithm_partial_monitoring_waterTransfer_fixed_mixture_compact_certificate
import Theorems.Thm_BanditAlgorithm_exists_pointwise_le_of_compact_convex_weighted_le
import Definitions.Def_PartialMonitoringAlgorithm26
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false

open scoped BigOperators
open Set

namespace BanditAlgorithm

noncomputable section

private lemma sq_div_convex_two
    (α β p₁ p₂ x₁ x₂ : ℝ)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) (hαβ : α + β = 1)
    (hp₁ : 0 < p₁) (hp₂ : 0 < p₂) :
    (α * x₁ + β * x₂) ^ 2 / (α * p₁ + β * p₂) ≤
      α * (x₁ ^ 2 / p₁) + β * (x₂ ^ 2 / p₂) := by
  have hp : 0 < α * p₁ + β * p₂ := by
    rcases hα.eq_or_lt with rfl | hαpos
    · have hβone : β = 1 := by linarith
      simpa [hβone] using hp₂
    · exact add_pos_of_pos_of_nonneg (mul_pos hαpos hp₁) (mul_nonneg hβ hp₂.le)
  rw [div_le_iff₀ hp, add_mul]
  have hidentity : α * (x₁ ^ 2 / p₁) * (α * p₁ + β * p₂) +
      β * (x₂ ^ 2 / p₂) * (α * p₁ + β * p₂) -
        (α * x₁ + β * x₂) ^ 2 =
      α * β * (p₂ * x₁ - p₁ * x₂) ^ 2 / (p₁ * p₂) := by
    field_simp [hp₁.ne', hp₂.ne']
    nlinarith [hαβ]
  have hnonneg : 0 ≤ α * β * (p₂ * x₁ - p₁ * x₂) ^ 2 / (p₁ * p₂) := by
    positivity
  linarith

private def PMEstimatorClosedAt
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (S : Finset (Fin k)) (s₀ : Fin k)
    (f : Fin k → 𝕊 → Fin k → ℝ) : Prop :=
  (∀ a σ b, b ∉ S → f a σ b = 0) ∧
  ∀ i b, b ∈ S →
    (∑ a, f a (G.Φ a i) b) - G.L b i =
      (∑ a, f a (G.Φ a i) s₀) - G.L s₀ i

private lemma pmEstimatorClosedAt_iff
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (S : Finset (Fin k))
    {s₀ : Fin k} (hs₀ : s₀ ∈ S) (f : Fin k → 𝕊 → Fin k → ℝ) :
    PMEstimatorClosedAt G S s₀ f ↔ PMVectorEstimatorOn G S f := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    intro i
    refine ⟨(∑ a, f a (G.Φ a i) s₀) - G.L s₀ i, ?_⟩
    intro b hb
    have := h.2 i b hb
    linarith
  · intro h
    refine ⟨h.1, ?_⟩
    intro i b hb
    obtain ⟨c, hc⟩ := h.2 i
    rw [hc b hb, hc s₀ hs₀]
    ring

private def pmWaterQuadSafe
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (q : Fin k → ℝ)
    (η δ : ℝ) (p : Fin k → ℝ) (f : Fin k → 𝕊 → Fin k → ℝ)
    (i : Fin d) : ℝ :=
  ∑ a : Fin k, max (p a) δ *
    (∑ b : Fin k, q b * (η * f a (G.Φ a i) b / max (p a) δ) ^ 2)

private abbrev PMWaterPair (k : ℕ) (𝕊 : Type*) :=
  (Fin k → ℝ) × (Fin k → 𝕊 → Fin k → ℝ)

private def pmWaterFeasible
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (S : Finset (Fin k)) (s₀ : Fin k)
    (q : Fin k → ℝ) (η δ V B : ℝ)
    (x : PMWaterPair k 𝕊) : Prop :=
  x.1 ∈ stdSimplex ℝ (Fin k) ∧
  (∀ a, δ ≤ x.1 a) ∧
  (∀ a σ b, |x.2 a σ b| ≤ V) ∧
  PMEstimatorClosedAt G S s₀ x.2 ∧
  (∀ a σ b, -x.1 a ≤ η * x.2 a σ b) ∧
  ∀ i, pmWaterQuadSafe G q η δ x.1 x.2 i ≤ η ^ 2 * B

private lemma isClosed_pmWaterFeasible
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (S : Finset (Fin k)) (s₀ : Fin k)
    (q : Fin k → ℝ) (η δ V B : ℝ) (hδ : 0 < δ) :
    IsClosed {x : PMWaterPair k 𝕊 |
      pmWaterFeasible G S s₀ q η δ V B x} := by
  let X0 : Set (PMWaterPair k 𝕊) := {x | x.1 ∈ stdSimplex ℝ (Fin k)}
  let X1 : Set (PMWaterPair k 𝕊) := {x | ∀ a, δ ≤ x.1 a}
  let X2 : Set (PMWaterPair k 𝕊) := {x | ∀ a σ b, |x.2 a σ b| ≤ V}
  let X3 : Set (PMWaterPair k 𝕊) := {x | PMEstimatorClosedAt G S s₀ x.2}
  let X4 : Set (PMWaterPair k 𝕊) := {x | ∀ a σ b, -x.1 a ≤ η * x.2 a σ b}
  let X5 : Set (PMWaterPair k 𝕊) :=
    {x | ∀ i, pmWaterQuadSafe G q η δ x.1 x.2 i ≤ η ^ 2 * B}
  have h0 : IsClosed X0 := by
    exact isClosed_stdSimplex ℝ (Fin k) |>.preimage (by fun_prop)
  have h1 : IsClosed X1 := by
    change IsClosed {x : PMWaterPair k 𝕊 | ∀ a, δ ≤ x.1 a}
    rw [setOf_forall]
    apply isClosed_iInter
    intro a
    exact isClosed_le (by fun_prop) (by fun_prop)
  have h2 : IsClosed X2 := by
    change IsClosed {x : PMWaterPair k 𝕊 | ∀ a σ b, |x.2 a σ b| ≤ V}
    rw [setOf_forall]
    apply isClosed_iInter
    intro a
    rw [setOf_forall]
    apply isClosed_iInter
    intro σ
    rw [setOf_forall]
    apply isClosed_iInter
    intro b
    exact isClosed_le (by fun_prop) (by fun_prop)
  have h3 : IsClosed X3 := by
    have hsupp : IsClosed {x : PMWaterPair k 𝕊 |
        ∀ a σ b, b ∉ S → x.2 a σ b = 0} := by
      change IsClosed {x : PMWaterPair k 𝕊 |
        ∀ a σ b, b ∉ S → x.2 a σ b = 0}
      rw [setOf_forall]
      apply isClosed_iInter
      intro a
      rw [setOf_forall]
      apply isClosed_iInter
      intro σ
      rw [setOf_forall]
      apply isClosed_iInter
      intro b
      by_cases hb : b ∈ S
      · simp [hb]
      · simpa [hb] using (isClosed_eq (f := fun x : PMWaterPair k 𝕊 => x.2 a σ b)
          (g := fun _ => (0 : ℝ)) (by fun_prop) (by fun_prop))
    have hcent : IsClosed {x : PMWaterPair k 𝕊 | ∀ i b, b ∈ S →
        (∑ a, x.2 a (G.Φ a i) b) - G.L b i =
          (∑ a, x.2 a (G.Φ a i) s₀) - G.L s₀ i} := by
      change IsClosed {x : PMWaterPair k 𝕊 | ∀ i b, b ∈ S →
        (∑ a, x.2 a (G.Φ a i) b) - G.L b i =
          (∑ a, x.2 a (G.Φ a i) s₀) - G.L s₀ i}
      rw [setOf_forall]
      apply isClosed_iInter
      intro i
      rw [setOf_forall]
      apply isClosed_iInter
      intro b
      by_cases hb : b ∈ S
      · simpa [hb] using (isClosed_eq
          (f := fun x : PMWaterPair k 𝕊 => (∑ a, x.2 a (G.Φ a i) b) - G.L b i)
          (g := fun x : PMWaterPair k 𝕊 => (∑ a, x.2 a (G.Φ a i) s₀) - G.L s₀ i)
          (by fun_prop) (by fun_prop))
      · simp [hb]
    simpa [X3, PMEstimatorClosedAt, Set.setOf_and] using hsupp.inter hcent
  have h4 : IsClosed X4 := by
    change IsClosed {x : PMWaterPair k 𝕊 | ∀ a σ b,
      -x.1 a ≤ η * x.2 a σ b}
    rw [setOf_forall]
    apply isClosed_iInter
    intro a
    rw [setOf_forall]
    apply isClosed_iInter
    intro σ
    rw [setOf_forall]
    apply isClosed_iInter
    intro b
    exact isClosed_le (by fun_prop) (by fun_prop)
  have hquad (i : Fin d) : Continuous
      (fun x : PMWaterPair k 𝕊 => pmWaterQuadSafe G q η δ x.1 x.2 i) := by
    unfold pmWaterQuadSafe
    apply continuous_finset_sum
    intro a ha
    apply Continuous.mul
    · fun_prop
    · apply continuous_finset_sum
      intro b hb
      apply Continuous.mul continuous_const
      apply Continuous.pow
      apply Continuous.div
      · fun_prop
      · fun_prop
      · intro x
        exact ne_of_gt (hδ.trans_le (le_max_right _ _))
  have h5 : IsClosed X5 := by
    change IsClosed {x : PMWaterPair k 𝕊 | ∀ i,
      pmWaterQuadSafe G q η δ x.1 x.2 i ≤ η ^ 2 * B}
    rw [setOf_forall]
    apply isClosed_iInter
    intro i
    exact isClosed_le (hquad i) continuous_const
  have hall := (((((h0.inter h1).inter h2).inter h3).inter h4).inter h5)
  simpa [X0, X1, X2, X3, X4, X5, pmWaterFeasible, Set.setOf_and,
    Set.inter_assoc] using hall

private lemma isBounded_pmWaterFeasible
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 0 < k)
    (S : Finset (Fin k)) (s₀ : Fin k)
    (q : Fin k → ℝ) (η δ V B : ℝ) :
    Bornology.IsBounded {x : PMWaterPair k 𝕊 |
      pmWaterFeasible G S s₀ q η δ V B x} := by
  let Pbox : Set (Fin k → ℝ) := Set.univ.pi fun _ => Set.Icc (0 : ℝ) 1
  let Fbox : Set (Fin k → 𝕊 → Fin k → ℝ) :=
    Set.univ.pi fun _ => Set.univ.pi fun _ => Set.univ.pi fun _ => Set.Icc (-V) V
  have hPbox : Bornology.IsBounded Pbox := by
    exact Bornology.IsBounded.pi fun _ => Metric.isBounded_Icc 0 1
  have hFbox : Bornology.IsBounded Fbox := by
    exact Bornology.IsBounded.pi fun _ => Bornology.IsBounded.pi fun _ =>
      Bornology.IsBounded.pi fun _ => Metric.isBounded_Icc (-V) V
  apply (hPbox.prod hFbox).subset
  intro x hx
  have hp := hx.1
  have hfbound := hx.2.2.1
  constructor
  · rw [Set.mem_pi]
    intro a ha
    refine ⟨hp.1 a, ?_⟩
    have hsingle := Finset.single_le_sum
      (s := Finset.univ) (f := x.1) (fun b _ => hp.1 b) (Finset.mem_univ a)
    simpa [hp.2] using hsingle
  · rw [Set.mem_pi]
    intro a ha
    rw [Set.mem_pi]
    intro σ hσ
    rw [Set.mem_pi]
    intro b hb
    exact abs_le.mp (hfbound a σ b)

private lemma convex_pmWaterFeasible
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊)
    (S : Finset (Fin k)) (s₀ : Fin k)
    (q : Fin k → ℝ) (hq0 : ∀ b, 0 ≤ q b)
    (η δ V B : ℝ) (hδ : 0 < δ) :
    Convex ℝ {x : PMWaterPair k 𝕊 |
      pmWaterFeasible G S s₀ q η δ V B x} := by
  intro x hx y hy α β hα hβ hαβ
  rcases hx with ⟨hxp, hxδ, hxV, hxest, hxstab, hxquad⟩
  rcases hy with ⟨hyp, hyδ, hyV, hyest, hystab, hyquad⟩
  have hxpos (a : Fin k) : 0 < x.1 a := hδ.trans_le (hxδ a)
  have hypos (a : Fin k) : 0 < y.1 a := hδ.trans_le (hyδ a)
  have hzδ (a : Fin k) : δ ≤ (α • x + β • y).1 a := by
    change δ ≤ α * x.1 a + β * y.1 a
    nlinarith [mul_le_mul_of_nonneg_left (hxδ a) hα,
      mul_le_mul_of_nonneg_left (hyδ a) hβ]
  refine ⟨?_, hzδ, ?_, ?_, ?_, ?_⟩
  · exact convex_stdSimplex ℝ (Fin k) hxp hyp hα hβ hαβ
  · intro a σ b
    change |α * x.2 a σ b + β * y.2 a σ b| ≤ V
    calc
      |α * x.2 a σ b + β * y.2 a σ b| ≤
          |α * x.2 a σ b| + |β * y.2 a σ b| := abs_add_le _ _
      _ = α * |x.2 a σ b| + β * |y.2 a σ b| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hα, abs_of_nonneg hβ]
      _ ≤ α * V + β * V := add_le_add
        (mul_le_mul_of_nonneg_left (hxV a σ b) hα)
        (mul_le_mul_of_nonneg_left (hyV a σ b) hβ)
      _ = V := by rw [← add_mul, hαβ, one_mul]
  · constructor
    · intro a σ b hb
      change α * x.2 a σ b + β * y.2 a σ b = 0
      rw [hxest.1 a σ b hb, hyest.1 a σ b hb]
      ring
    · intro i b hb
      have hxEq := hxest.2 i b hb
      have hyEq := hyest.2 i b hb
      change
        (∑ a, (α * x.2 a (G.Φ a i) b + β * y.2 a (G.Φ a i) b)) - G.L b i =
          (∑ a, (α * x.2 a (G.Φ a i) s₀ + β * y.2 a (G.Φ a i) s₀)) - G.L s₀ i
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      calc
        α * (∑ a, x.2 a (G.Φ a i) b) + β * (∑ a, y.2 a (G.Φ a i) b) -
              G.L b i =
            α * ((∑ a, x.2 a (G.Φ a i) b) - G.L b i) +
              β * ((∑ a, y.2 a (G.Φ a i) b) - G.L b i) := by
                linear_combination (G.L b i) * hαβ
        _ = α * ((∑ a, x.2 a (G.Φ a i) s₀) - G.L s₀ i) +
              β * ((∑ a, y.2 a (G.Φ a i) s₀) - G.L s₀ i) := by
                rw [hxEq, hyEq]
        _ = α * (∑ a, x.2 a (G.Φ a i) s₀) + β * (∑ a, y.2 a (G.Φ a i) s₀) -
              G.L s₀ i := by
                linear_combination -(G.L s₀ i) * hαβ
  · intro a σ b
    change -(α * x.1 a + β * y.1 a) ≤
      η * (α * x.2 a σ b + β * y.2 a σ b)
    nlinarith [mul_le_mul_of_nonneg_left (hxstab a σ b) hα,
      mul_le_mul_of_nonneg_left (hystab a σ b) hβ]
  · intro i
    have hmaxx (a : Fin k) : max (x.1 a) δ = x.1 a := max_eq_left (hxδ a)
    have hmaxy (a : Fin k) : max (y.1 a) δ = y.1 a := max_eq_left (hyδ a)
    have hmaxz (a : Fin k) : max (α * x.1 a + β * y.1 a) δ =
        α * x.1 a + β * y.1 a := by
      apply max_eq_left
      exact hzδ a
    have hterm (a b : Fin k) :
        (α * x.1 a + β * y.1 a) *
            (q b * (η * (α * x.2 a (G.Φ a i) b + β * y.2 a (G.Φ a i) b) /
              (α * x.1 a + β * y.1 a)) ^ 2) ≤
          α * (x.1 a * (q b * (η * x.2 a (G.Φ a i) b / x.1 a) ^ 2)) +
          β * (y.1 a * (q b * (η * y.2 a (G.Φ a i) b / y.1 a) ^ 2)) := by
      have hs := sq_div_convex_two α β (x.1 a) (y.1 a)
        (η * x.2 a (G.Φ a i) b) (η * y.2 a (G.Φ a i) b)
        hα hβ hαβ (hxpos a) (hypos a)
      have hs' := mul_le_mul_of_nonneg_left hs (hq0 b)
      have hzpos : 0 < α * x.1 a + β * y.1 a := by
        rcases hα.eq_or_lt with rfl | hαpos
        · have hβone : β = 1 := by linarith
          simpa [hβone] using hypos a
        · exact add_pos_of_pos_of_nonneg (mul_pos hαpos (hxpos a))
            (mul_nonneg hβ (hypos a).le)
      field_simp [hzpos.ne', (hxpos a).ne', (hypos a).ne'] at hs' ⊢
      nlinarith
    unfold pmWaterQuadSafe
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    simp only [hmaxz]
    change
      (∑ a, (α * x.1 a + β * y.1 a) *
        ∑ b, q b *
          (η * (α * x.2 a (G.Φ a i) b + β * y.2 a (G.Φ a i) b) /
            (α * x.1 a + β * y.1 a)) ^ 2) ≤ η ^ 2 * B
    calc
      _ = ∑ a, ∑ b, (α * x.1 a + β * y.1 a) *
          (q b * (η * (α * x.2 a (G.Φ a i) b + β * y.2 a (G.Φ a i) b) /
            (α * x.1 a + β * y.1 a)) ^ 2) := by
              apply Finset.sum_congr rfl
              intro a ha
              rw [Finset.mul_sum]
      _ ≤ ∑ a, ∑ b,
          (α * (x.1 a * (q b * (η * x.2 a (G.Φ a i) b / x.1 a) ^ 2)) +
           β * (y.1 a * (q b * (η * y.2 a (G.Φ a i) b / y.1 a) ^ 2))) := by
              exact Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hterm a b
      _ = α * (∑ a, x.1 a *
            (∑ b, q b * (η * x.2 a (G.Φ a i) b / x.1 a) ^ 2)) +
          β * (∑ a, y.1 a *
            (∑ b, q b * (η * y.2 a (G.Φ a i) b / y.1 a) ^ 2)) := by
              simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ α * (η ^ 2 * B) + β * (η ^ 2 * B) := add_le_add
          (mul_le_mul_of_nonneg_left (by simpa [pmWaterQuadSafe, hmaxx] using hxquad i) hα)
          (mul_le_mul_of_nonneg_left (by simpa [pmWaterQuadSafe, hmaxy] using hyquad i) hβ)
      _ = η ^ 2 * B := by rw [← add_mul, hαβ, one_mul]

private theorem exists_pointwise_le_of_compact_convex_weighted_le_affine
    {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fintype I] [Nonempty I]
    (X : Set E) (hXne : X.Nonempty) (hXconv : Convex ℝ X) (hXcomp : IsCompact X)
    (g : E → I → ℝ)
    (hgcont : ∀ i, Continuous fun x => g x i)
    (hgaff : ∀ x y : E, ∀ α β : ℝ, α + β = 1 →
      ∀ i, g (α • x + β • y) i = α * g x i + β * g y i)
    (C : ℝ)
    (hweighted : ∀ lam : I → ℝ, lam ∈ stdSimplex ℝ I →
      ∃ x ∈ X, ∑ i : I, lam i * g x i ≤ C) :
    ∃ x ∈ X, ∀ i : I, g x i ≤ C := by
  classical
  let Y : Set (I → ℝ) := stdSimplex ℝ I
  let F : E → (I → ℝ) → ℝ := fun x lam => ∑ i : I, lam i * g x i
  have hYne : Y.Nonempty := by
    let i₀ : I := Classical.choice inferInstance
    exact ⟨Pi.single i₀ 1, single_mem_stdSimplex ℝ i₀⟩
  have hYconv : Convex ℝ Y := convex_stdSimplex ℝ I
  have hYcomp : IsCompact Y := isCompact_stdSimplex ℝ I
  have hFx_cont : ∀ x ∈ X, ContinuousOn (fun lam => F x lam) Y := by
    intro x hx
    apply Continuous.continuousOn
    dsimp [F]
    fun_prop
  have hFx_conc : ∀ x ∈ X, ConcaveOn ℝ Y (fun lam => F x lam) := by
    intro x hx
    refine ⟨hYconv, ?_⟩
    intro a ha b hb α β hα hβ hαβ
    dsimp [F]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply le_of_eq
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hFy_cont : ∀ lam ∈ Y, ContinuousOn (fun x => F x lam) X := by
    intro lam hlam
    apply Continuous.continuousOn
    dsimp [F]
    exact continuous_finset_sum _ fun i _ => continuous_const.mul (hgcont i)
  have hFy_conv : ∀ lam ∈ Y, ConvexOn ℝ X (fun x => F x lam) := by
    intro lam hlam
    refine ⟨hXconv, ?_⟩
    intro x hx y hy α β hα hβ hαβ
    dsimp [F]
    rw [Finset.mul_sum, Finset.mul_sum]
    apply le_of_eq
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hgaff x y α β hαβ i]
    ring
  obtain ⟨x₀, hx₀, lam₀, hlam₀, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn hXne hXconv hXcomp
      (fun lam hlam => (hFy_cont lam hlam).lowerSemicontinuousOn)
      (fun lam hlam => (hFy_conv lam hlam).quasiconvexOn)
      hYconv hYne hYcomp
      (fun x hx => (hFx_cont x hx).upperSemicontinuousOn)
      (fun x hx => (hFx_conc x hx).quasiconcaveOn)
  obtain ⟨x₁, hx₁, hx₁C⟩ := hweighted lam₀ hlam₀
  refine ⟨x₀, hx₀, ?_⟩
  intro i
  let e : I → ℝ := Pi.single i 1
  have he : e ∈ Y := single_mem_stdSimplex ℝ i
  have hleft := hsaddle x₁ hx₁ e he
  have hxe : F x₀ e = g x₀ i := by
    dsimp [F, e]
    rw [Fintype.sum_eq_single i, Pi.single_eq_same, one_mul]
    intro j hji
    simp [Pi.single_apply, hji]
  exact hxe ▸ hleft.trans hx₁C

private theorem uniformize_pmWaterFeasible
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊] [Nonempty (Fin d)]
    (G : PartialMonitoringGame k d 𝕊)
    (S : Finset (Fin k)) {s₀ : Fin k} (hs₀ : s₀ ∈ S)
    (q : Fin k → ℝ) (hq0 : ∀ b, 0 ≤ q b)
    (η δ V B C : ℝ) (hδ : 0 < δ)
    (hweighted : ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
      ∃ x : PMWaterPair k 𝕊,
        pmWaterFeasible G S s₀ q η δ V B x ∧
        ∑ i : Fin d, lam i *
          (∑ a : Fin k, (x.1 a - q a) * G.L a i) ≤ C) :
    ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
      PMInteriorDistribution p ∧ PMVectorEstimatorOn G S f ∧
      (∀ i : Fin d, ∑ a : Fin k, (p a - q a) * G.L a i ≤ C) ∧
      (∀ a σ b, -1 ≤ η * f a σ b / p a) ∧
      ∀ i : Fin d,
        ∑ a : Fin k, p a *
          (∑ b : Fin k, q b * (η * f a (G.Φ a i) b / p a) ^ 2) ≤
            η ^ 2 * B := by
  classical
  let X : Set (PMWaterPair k 𝕊) :=
    {x | pmWaterFeasible G S s₀ q η δ V B x}
  let g : PMWaterPair k 𝕊 → Fin d → ℝ := fun x i =>
    ∑ a : Fin k, (x.1 a - q a) * G.L a i
  have hgcont (i : Fin d) : Continuous fun x : PMWaterPair k 𝕊 => g x i := by
    dsimp [g]
    fun_prop
  have hgaff (x y : PMWaterPair k 𝕊) (α β : ℝ) (hαβ : α + β = 1) (i : Fin d) :
      g (α • x + β • y) i = α * g x i + β * g y i := by
    dsimp [g]
    simp only [Prod.fst_add, Prod.smul_fst, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    have hmul := congrArg (fun t : ℝ => t * (q a * G.L a i)) hαβ
    ring_nf at hmul ⊢
    linarith
  have hXne : X.Nonempty := by
    let i₀ : Fin d := Classical.choice inferInstance
    let lam : Fin d → ℝ := Pi.single i₀ 1
    have hlam : lam ∈ stdSimplex ℝ (Fin d) := single_mem_stdSimplex ℝ i₀
    obtain ⟨x, hx, hw⟩ := hweighted lam hlam
    exact ⟨x, hx⟩
  have hXclosed : IsClosed X :=
    isClosed_pmWaterFeasible G S s₀ q η δ V B hδ
  have hXbounded : Bornology.IsBounded X :=
    isBounded_pmWaterFeasible G (by
      have := hs₀
      exact Fin.pos_iff_nonempty.mpr ⟨s₀⟩) S s₀ q η δ V B
  have hXcomp : IsCompact X :=
    Metric.isCompact_of_isClosed_isBounded hXclosed hXbounded
  have hXconv : Convex ℝ X :=
    convex_pmWaterFeasible G S s₀ q hq0 η δ V B hδ
  have hwg : ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
      ∃ x ∈ X, ∑ i : Fin d, lam i * g x i ≤ C := by
    intro lam hlam
    obtain ⟨x, hx, hw⟩ := hweighted lam hlam
    refine ⟨x, hx, ?_⟩
    simpa [g] using hw
  obtain ⟨x, hx, hpoint⟩ :=
    exists_pointwise_le_of_compact_convex_weighted_le_affine X hXne hXconv hXcomp
      g hgcont hgaff C hwg
  rcases hx with ⟨hp, hpδ, hfV, hfest, hstab, hquad⟩
  have hpPos (a : Fin k) : 0 < x.1 a := hδ.trans_le (hpδ a)
  refine ⟨x.1, x.2, ⟨hp, hpPos⟩,
    (pmEstimatorClosedAt_iff G S hs₀ x.2).mp hfest, ?_, ?_, ?_⟩
  · intro i
    simpa [g] using hpoint i
  · intro a σ b
    apply (le_div_iff₀ (hpPos a)).mpr
    simpa [neg_mul] using hstab a σ b
  · intro i
    have hmax (a : Fin k) : max (x.1 a) δ = x.1 a := max_eq_left (hpδ a)
    simpa [pmWaterQuadSafe, hmax] using hquad i

theorem locally_observable_water_transfer_certificate_proof
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hd : 0 < d)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (hloc : LocallyObservable G) :
    ∃ S : Finset (Fin k), ∃ K η₀ : ℝ,
      S.Nonempty ∧ 0 ≤ K ∧ 0 < η₀ ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ q : Fin k → ℝ, PMSupportedOn S q →
          ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
            PMInteriorDistribution p ∧ PMVectorEstimatorOn G S f ∧
            (∀ i : Fin d,
              ∑ a : Fin k, (p a - q a) * G.L a i ≤ η * K) ∧
            (∀ a σ b, -1 ≤ η * f a σ b / p a) ∧
            ∀ i : Fin d,
              ∑ a : Fin k, p a *
                (∑ b : Fin k, q b * (η * f a (G.Φ a i) b / p a) ^ 2) ≤
                  η ^ 2 * K := by
  classical
  obtain ⟨S, V, hSne, hV, hbest, hmono⟩ :=
    partial_monitoring_locally_observable_monotone_vector_estimator G hk hd hloc
  let W : ℝ := max 1 V
  let A : ℝ := (k : ℝ) * W
  let B : ℝ := 2 * (k : ℝ) ^ 3 * W ^ 2
  let K : ℝ := max A B
  let η₀ : ℝ := 1 / (2 * A)
  have hkpos : 0 < k := lt_of_lt_of_le (by decide : 0 < 2) hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast hkpos
  have hWpos : 0 < W := lt_of_lt_of_le zero_lt_one (le_max_left 1 V)
  have hApos : 0 < A := mul_pos hkR hWpos
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hK0 : 0 ≤ K := hApos.le.trans (le_max_left A B)
  have hη₀pos : 0 < η₀ := by dsimp [η₀]; positivity
  refine ⟨S, K, η₀, hSne, hK0, hη₀pos, hbest, ?_⟩
  intro η hη hηle q hq
  haveI : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let s₀ : Fin k := hSne.choose
  have hs₀ : s₀ ∈ S := hSne.choose_spec
  let δ : ℝ := η * W
  have hδ : 0 < δ := mul_pos hη hWpos
  have hηsmall : η * ((k : ℝ) * max 1 V) ≤ 1 / 2 := by
    have hηA : η * A ≤ η₀ * A := mul_le_mul_of_nonneg_right hηle hApos.le
    have hη₀A : η₀ * A = 1 / 2 := by
      dsimp [η₀]
      field_simp [hApos.ne']
    simpa [A, W] using hηA.trans_eq hη₀A
  have hweighted : ∀ lam : Fin d → ℝ, lam ∈ stdSimplex ℝ (Fin d) →
      ∃ x : PMWaterPair k 𝕊,
        pmWaterFeasible G S s₀ q η δ V B x ∧
        ∑ i : Fin d, lam i *
          (∑ a : Fin k, (x.1 a - q a) * G.L a i) ≤ η * A := by
    intro lam hlam
    obtain ⟨f₀, hfvec, hfbound, hfmono⟩ := hmono lam hlam
    let anc : Fin k → Finset (Fin k) := fun b =>
      Finset.univ.filter fun a =>
        ∑ i : Fin d, G.L a i * lam i ≤ ∑ i : Fin d, G.L b i * lam i
    have hself (b : Fin k) : b ∈ anc b := by simp [anc]
    have htrans : ∀ a b, a ∈ anc b → ∀ c, b ∈ anc c → a ∈ anc c := by
      intro a b hab c hbc
      simp only [anc, Finset.mem_filter, Finset.mem_univ, true_and] at hab hbc ⊢
      exact hab.trans hbc
    have hfsupp : ∀ a σ b, f₀ a σ b ≠ 0 → a ∈ anc b := by
      intro a σ b hne
      simp only [anc, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hfmono a σ b hne
    have hloss : ∀ a b, a ∈ anc b →
        ∑ i : Fin d, G.L a i * lam i ≤ ∑ i : Fin d, G.L b i * lam i := by
      intro a b hab
      simpa [anc] using hab
    obtain ⟨p, f, hp, hf, hpδ, hfV, hstab, hquad, hlossmix⟩ :=
      partial_monitoring_waterTransfer_fixed_mixture_compact_certificate
        G hk hL S q hq lam hlam anc hself htrans f₀ hfvec V hV hfbound hfsupp
          hloss η hη hηsmall
    refine ⟨(p, f), ?_, ?_⟩
    · refine ⟨hp.1, ?_, hfV, (pmEstimatorClosedAt_iff G S hs₀ f).mpr hf, ?_, ?_⟩
      · intro a
        simpa [δ, W] using hpδ a
      · intro a σ b
        have hs := (le_div_iff₀ (hp.2 a)).mp (hstab a σ b)
        change -p a ≤ η * f a σ b
        simpa using hs
      · intro i
        have hmax (a : Fin k) : max (p a) δ = p a := by
          apply max_eq_left
          simpa [δ, W] using hpδ a
        simpa [pmWaterQuadSafe, hmax, B, W] using hquad i
    · simpa [A, W] using hlossmix
  obtain ⟨p, f, hp, hf, hloss, hstab, hquad⟩ :=
    uniformize_pmWaterFeasible G S hs₀ q hq.1.1 η δ V B (η * A) hδ hweighted
  refine ⟨p, f, hp, hf, ?_, hstab, ?_⟩
  · intro i
    exact (hloss i).trans (mul_le_mul_of_nonneg_left (le_max_left A B) hη.le)
  · intro i
    exact (hquad i).trans (mul_le_mul_of_nonneg_left (le_max_right A B) (sq_nonneg η))

end
end BanditAlgorithm

theorem solution
    {k d : ℕ} {𝕊 : Type*} [Fintype 𝕊]
    (G : BanditAlgorithm.PartialMonitoringGame k d 𝕊) (hk : 2 ≤ k)
    (hd : 0 < d)
    (hL : ∀ a i, G.L a i ∈ Set.Icc (0 : ℝ) 1)
    (hloc : BanditAlgorithm.LocallyObservable G) :
    ∃ S : Finset (Fin k), ∃ K η₀ : ℝ,
      S.Nonempty ∧ 0 ≤ K ∧ 0 < η₀ ∧
      (∀ (n : ℕ) (i : Fin n → Fin d), ∃ b ∈ S, ∀ a : Fin k,
        ∑ t, G.L b (i t) ≤ ∑ t, G.L a (i t)) ∧
      ∀ η : ℝ, 0 < η → η ≤ η₀ →
        ∀ q : Fin k → ℝ, BanditAlgorithm.PMSupportedOn S q →
          ∃ p : Fin k → ℝ, ∃ f : Fin k → 𝕊 → Fin k → ℝ,
            BanditAlgorithm.PMInteriorDistribution p ∧
            BanditAlgorithm.PMVectorEstimatorOn G S f ∧
            (∀ i : Fin d,
              ∑ a : Fin k, (p a - q a) * G.L a i ≤ η * K) ∧
            (∀ a σ b, -1 ≤ η * f a σ b / p a) ∧
            ∀ i : Fin d,
              ∑ a : Fin k, p a *
                (∑ b : Fin k, q b * (η * f a (G.Φ a i) b / p a) ^ 2) ≤
                  η ^ 2 * K :=
  BanditAlgorithm.locally_observable_water_transfer_certificate_proof G hk hd hL hloc
