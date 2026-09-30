-- Prove2me | solution 1 for LinearOptimization.lp_unbounded_iff_extreme_ray
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:08:03.972413+00:00
-- url     : https://prove2.me/submissions/2e61b353-effd-4bfb-9028-9416ef3b4712

import Mathlib.Analysis.Convex.Extreme
import Mathlib
import Definitions.Def_LinearOptimization_RecessionCone
import Definitions.Def_Polyhedron
import Definitions.Def_ContainsLine
import Definitions.Def_Vertex
import Definitions.Def_BasicSolution
import Definitions.Def_ActiveConstraints
import Definitions.Def_FourierMotzkinStep

/- Accepted Prove2Me helper 035b04e5-ef48-4d7a-9b6f-3a7d2181aa70, submission 9c2718ff-39b9-4360-a2d7-b6047832b301, author MKPynnic. -/
section R6RayHelper0
open Matrix LinearOptimization

/-- Every linear functional on `Fin n → ℝ` is `v ↦ v ⬝ᵥ d` for a unique `d`. -/
private lemma r6ray_0_dual_eq_dotProduct {n : ℕ} (f : Module.Dual ℝ (Fin n → ℝ)) :
    ∃ d : Fin n → ℝ, ∀ v, f v = v ⬝ᵥ d := by
  classical
  refine ⟨fun j => f (Pi.single j 1), fun v => ?_⟩
  have hv : v = ∑ j, v j • (Pi.single j (1 : ℝ)) := by
    ext k
    simp [Finset.sum_apply, Pi.single_apply, Finset.sum_ite_eq]
  calc f v = f (∑ j, v j • (Pi.single j (1 : ℝ))) := by rw [← hv]
    _ = ∑ j, v j * f (Pi.single j 1) := by
        rw [map_sum]; exact Finset.sum_congr rfl fun j _ => by rw [map_smul]; simp [smul_eq_mul]
    _ = v ⬝ᵥ (fun j => f (Pi.single j 1)) := rfl

/-- The subspace of vectors orthogonal to a fixed `d`. -/
private def r6ray_0_orthTo {n : ℕ} (d : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | v ⬝ᵥ d = 0}
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, add_dotProduct] at *
    rw [hu, hv, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_setOf_eq, smul_dotProduct] at *
    rw [hv, smul_zero]

theorem LinearOptimization.lp_active_constraint_equiv {ι : Type} [Fintype ι] {n : ℕ}
    (C : ι → LinearConstraint n) (x' : Fin n → ℝ) :
    List.TFAE
      [ ∃ s : Finset ι, s.card = n ∧ (∀ i ∈ s, (C i).IsActiveAt x') ∧
          LinearIndependent ℝ (fun i : s => (C i.1).a),
        Submodule.span ℝ ((fun i => (C i).a) '' {i | (C i).IsActiveAt x'}) = ⊤,
        ∀ y : Fin n → ℝ,
          (∀ i, (C i).IsActiveAt x' → (C i).a ⬝ᵥ y = (C i).b) → y = x' ] := by
  classical
  have hfr : Module.finrank ℝ (Fin n → ℝ) = n := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  -- The image of the active constraint vectors.
  set S : Set (Fin n → ℝ) := (fun i => (C i).a) '' {i | (C i).IsActiveAt x'} with hS
  tfae_have 1 → 2 := by
    rintro ⟨s, hcard, hact, hli⟩
    have hcard' : Fintype.card {i // i ∈ s} = Module.finrank ℝ (Fin n → ℝ) := by
      rw [Fintype.card_coe, hcard, hfr]
    have htop : Submodule.span ℝ (Set.range (fun i : s => (C i.1).a)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' hcard'
    refine top_le_iff.mp ?_
    rw [← htop]
    refine Submodule.span_mono ?_
    rintro w ⟨i, rfl⟩
    exact ⟨i.1, hact i.1 i.2, rfl⟩
  tfae_have 2 → 3 := by
    intro h2 y hy
    have hmem : ∀ v : Fin n → ℝ, v ⬝ᵥ (y - x') = 0 := by
      have hsub : S ⊆ (r6ray_0_orthTo (y - x') : Set (Fin n → ℝ)) := by
        rintro w ⟨i, hi, rfl⟩
        have h1 : (C i).a ⬝ᵥ x' = (C i).b := hi
        have h2' : (C i).a ⬝ᵥ y = (C i).b := hy i hi
        show (C i).a ⬝ᵥ (y - x') = 0
        rw [dotProduct_sub, h1, h2', sub_self]
      have : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ r6ray_0_orthTo (y - x') := by
        rw [← h2]; exact Submodule.span_le.mpr hsub
      intro v; exact this (Submodule.mem_top)
    have hzero : (y - x') = 0 := dotProduct_self_eq_zero.mp (hmem (y - x'))
    exact sub_eq_zero.mp hzero
  tfae_have 3 → 1 := by
    intro h3
    -- Step A: the active vectors span everything.
    have h2 : Submodule.span ℝ S = ⊤ := by
      by_contra hne
      obtain ⟨f, hf0, hfmap⟩ :=
        Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
      obtain ⟨d, hd⟩ := r6ray_0_dual_eq_dotProduct f
      have hzero : ∀ i, (C i).IsActiveAt x' → (C i).a ⬝ᵥ d = 0 := by
        intro i hi
        have : (C i).a ∈ Submodule.span ℝ S := Submodule.subset_span ⟨i, hi, rfl⟩
        have : f ((C i).a) ∈ Submodule.map f (Submodule.span ℝ S) :=
          Submodule.mem_map_of_mem this
        rw [hfmap, Submodule.mem_bot] at this
        rw [← hd]; exact this
      have hy : ∀ i, (C i).IsActiveAt x' → (C i).a ⬝ᵥ (x' + d) = (C i).b := by
        intro i hi
        rw [dotProduct_add, hzero i hi, add_zero]; exact hi
      have hxd : x' + d = x' := h3 (x' + d) hy
      have hd0 : d = 0 := by
        have := hxd
        simpa using congrArg (fun z => z - x') this
      refine hf0 (LinearMap.ext fun v => ?_)
      simp [hd v, hd0]
    -- Step B: extract `n` independent active vectors.
    set A : Set ι := {i | (C i).IsActiveAt x'} with hA
    set v : A → (Fin n → ℝ) := fun i => (C i.1).a with hv
    have hrange : Set.range v = S := by
      ext w
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i.1, i.2, rfl⟩
      · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
    obtain ⟨κ, α, hαinj, hspan, hli⟩ := exists_linearIndependent' ℝ v
    have hκtop : Submodule.span ℝ (Set.range (v ∘ α)) = ⊤ := by
      rw [hspan, hrange, h2]
    have : Finite κ := Finite.of_injective α hαinj
    haveI : Fintype κ := Fintype.ofFinite κ
    let bas : Module.Basis κ ℝ (Fin n → ℝ) := Module.Basis.mk hli (le_of_eq hκtop.symm)
    have hcardκ : Fintype.card κ = n := by
      have h := Module.finrank_eq_card_basis bas
      rw [hfr] at h
      exact h.symm
    -- assemble the finset
    have hinj : Function.Injective (fun k : κ => (α k).1) := by
      intro k₁ k₂ h
      exact hαinj (Subtype.ext h)
    refine ⟨Finset.image (fun k : κ => (α k).1) Finset.univ, ?_, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, hcardκ]
    · intro i hi
      simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi
      obtain ⟨k, rfl⟩ := hi
      exact (α k).2
    · have hbij : Function.Bijective
          (fun k : κ => (⟨(α k).1, by simp⟩ : {i // i ∈ Finset.image (fun k : κ => (α k).1) Finset.univ})) := by
        constructor
        · intro k₁ k₂ h
          have hv : (α k₁).1 = (α k₂).1 := by simpa [Subtype.ext_iff] using h
          exact hinj hv
        · rintro ⟨i, hi⟩
          simp only [Finset.mem_image, Finset.mem_univ, true_and] at hi
          obtain ⟨k, hk⟩ := hi
          exact ⟨k, Subtype.ext hk⟩
      let e : κ ≃ {i // i ∈ Finset.image (fun k : κ => (α k).1) Finset.univ} :=
        Equiv.ofBijective _ hbij
      rw [← linearIndependent_equiv e]
      exact hli
  tfae_finish
end R6RayHelper0

/- Accepted Prove2Me helper 7d1d3dcc-c20d-44a2-bf8d-e9fe8403b941, submission df09e489-5f6a-42fb-9212-0b00df6b503e, author MKPynnic. -/
section R6RayHelper1
open Matrix LinearOptimization

/-- The subspace of vectors orthogonal to a fixed `d`. -/
private def r6ray_1_orthTo {n : ℕ} (d : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) where
  carrier := {v | v ⬝ᵥ d = 0}
  add_mem' := by
    intro u v hu hv
    simp only [Set.mem_setOf_eq, add_dotProduct] at *
    rw [hu, hv, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c v hv
    simp only [Set.mem_setOf_eq, smul_dotProduct] at *
    rw [hv, smul_zero]

/-- `n` linearly independent active constraints pin down at most one point
(uniqueness half of B&T Theorem 2.2). -/
private lemma r6ray_1_unique_of_indep {ι : Type} {n : ℕ} (C : ι → LinearConstraint n) (s : Finset ι)
    (hcard : s.card = n) (hli : LinearIndependent ℝ (fun i : s => (C i.1).a))
    {x y : Fin n → ℝ} (hx : ∀ i ∈ s, (C i).a ⬝ᵥ x = (C i).b)
    (hy : ∀ i ∈ s, (C i).a ⬝ᵥ y = (C i).b) : x = y := by
  have hfr : Module.finrank ℝ (Fin n → ℝ) = n := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  have hspan : Submodule.span ℝ (Set.range (fun i : s => (C i.1).a)) = ⊤ :=
    hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_coe, hcard, hfr])
  have hsub : Set.range (fun i : s => (C i.1).a) ⊆ (r6ray_1_orthTo (x - y) : Set (Fin n → ℝ)) := by
    rintro w ⟨i, rfl⟩
    show (C i.1).a ⬝ᵥ (x - y) = 0
    rw [dotProduct_sub, hx i.1 i.2, hy i.1 i.2, sub_self]
  have htop : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ r6ray_1_orthTo (x - y) := by
    rw [← hspan]; exact Submodule.span_le.mpr hsub
  have : (x - y) ⬝ᵥ (x - y) = 0 := htop (Submodule.mem_top)
  exact sub_eq_zero.mp (dotProduct_self_eq_zero.mp this)

theorem LinearOptimization.lp_vertex_extreme_bfs_equiv {ι : Type} [Fintype ι] {n : ℕ}
    (C : ι → LinearConstraint n) (x' : Fin n → ℝ)
    (hne : (constraintSet C).Nonempty) (hx : x' ∈ constraintSet C) :
    List.TFAE
      [ IsVertex (constraintSet C) x',
        x' ∈ Set.extremePoints ℝ (constraintSet C),
        IsBasicFeasibleSolution C x' ] := by
  classical
  -- A feasible point activates every equality constraint.
  have heq_active : ∀ i, (C i).rel = .eq → (C i).IsActiveAt x' := by
    intro i hi
    have h := hx i
    show (C i).a ⬝ᵥ x' = (C i).b
    simp only [LinearConstraint.IsSatisfiedAt, hi] at h
    exact h
  tfae_have 1 → 2 := by
    rintro ⟨hmem, c, hc⟩
    refine ⟨hmem, ?_⟩
    intro y hy z hz hseg
    obtain ⟨a, b, ha, hb, hab, hxeq⟩ := hseg
    have key : ∀ w ∈ constraintSet C, c ⬝ᵥ x' ≤ c ⬝ᵥ w := by
      intro w hw
      rcases eq_or_ne w x' with rfl | hne'
      · exact le_refl _
      · exact (hc w hw hne').le
    have hy' : c ⬝ᵥ x' ≤ c ⬝ᵥ y := key y hy
    have hz' : c ⬝ᵥ x' ≤ c ⬝ᵥ z := key z hz
    have hsum : c ⬝ᵥ x' = a * (c ⬝ᵥ y) + b * (c ⬝ᵥ z) := by
      rw [← hxeq, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
    by_contra hne'
    have hlt := hc y hy hne'
    have h1 : a * (c ⬝ᵥ x') < a * (c ⬝ᵥ y) := mul_lt_mul_of_pos_left hlt ha
    have h2 : b * (c ⬝ᵥ x') ≤ b * (c ⬝ᵥ z) := mul_le_mul_of_nonneg_left hz' hb.le
    have h3 : a * (c ⬝ᵥ x') + b * (c ⬝ᵥ x') = c ⬝ᵥ x' := by
      rw [← add_mul, hab, one_mul]
    linarith
  tfae_have 3 → 1 := by
    rintro ⟨⟨heq, s, hcard, hact, hli⟩, hmem⟩
    refine ⟨hmem, ?_⟩
    set σ : ι → ℝ := fun i => if (C i).rel = ConstraintRel.le then -1 else 1 with hσ
    have hσne : ∀ i, σ i ≠ 0 := by
      intro i; rw [hσ]; dsimp only; split <;> norm_num
    refine ⟨∑ i ∈ s, σ i • (C i).a, ?_⟩
    intro y hy hyne
    -- every feasible point beats the active right-hand sides, coordinate by coordinate
    have hle : ∀ i ∈ s, σ i * (C i).b ≤ σ i * ((C i).a ⬝ᵥ y) := by
      intro i _
      have hsat := hy i
      rcases hr : (C i).rel with _ | _ | _
      · have hs1 : σ i = 1 := by simp [hσ, hr]
        simp only [LinearConstraint.IsSatisfiedAt, hr] at hsat
        rw [hs1]; linarith
      · have hs1 : σ i = -1 := by simp [hσ, hr]
        simp only [LinearConstraint.IsSatisfiedAt, hr] at hsat
        rw [hs1]; linarith
      · have hs1 : σ i = 1 := by simp [hσ, hr]
        simp only [LinearConstraint.IsSatisfiedAt, hr] at hsat
        rw [hs1]; linarith
    have hx_eq : (∑ i ∈ s, σ i • (C i).a) ⬝ᵥ x' = ∑ i ∈ s, σ i * (C i).b := by
      rw [sum_dotProduct]
      exact Finset.sum_congr rfl fun i hi => by
        rw [smul_dotProduct, smul_eq_mul, hact i hi]
    have hy_eq : (∑ i ∈ s, σ i • (C i).a) ⬝ᵥ y = ∑ i ∈ s, σ i * ((C i).a ⬝ᵥ y) := by
      rw [sum_dotProduct]
      exact Finset.sum_congr rfl fun i _ => by rw [smul_dotProduct, smul_eq_mul]
    rw [hx_eq, hy_eq]
    rcases lt_or_eq_of_le (Finset.sum_le_sum hle) with h | h
    · exact h
    · exfalso
      have hterm : ∀ i ∈ s, (C i).a ⬝ᵥ y = (C i).b := by
        intro i hi
        by_contra hne2
        have hlt : σ i * (C i).b < σ i * ((C i).a ⬝ᵥ y) :=
          lt_of_le_of_ne (hle i hi) (fun hEq => hne2 (by
            have := mul_left_cancel₀ (hσne i) hEq
            exact this.symm))
        have := Finset.sum_lt_sum hle ⟨i, hi, hlt⟩
        linarith
      exact hyne (r6ray_1_unique_of_indep C s hcard hli hterm (fun i hi => hact i hi))
  tfae_have 2 → 3 := by
    intro hext
    by_contra hnbfs
    have hnb : ¬ IsBasicSolution C x' := fun h => hnbfs ⟨h, hx⟩
    have hns : ¬ ∃ s : Finset ι, s.card = n ∧ (∀ i ∈ s, (C i).IsActiveAt x') ∧
        LinearIndependent ℝ (fun i : s => (C i.1).a) := fun h => hnb ⟨heq_active, h⟩
    -- Theorem 2.2: failing (a) means the uniqueness statement (c) also fails.
    have hn3 : ¬ (∀ y : Fin n → ℝ,
        (∀ i, (C i).IsActiveAt x' → (C i).a ⬝ᵥ y = (C i).b) → y = x') := by
      intro h3
      exact hns (((lp_active_constraint_equiv C x').out 2 0).mp h3)
    push_neg at hn3
    obtain ⟨y0, hy0, hy0ne⟩ := hn3
    set d : Fin n → ℝ := y0 - x' with hdd
    have hd0 : d ≠ 0 := sub_ne_zero.mpr hy0ne
    have hdorth : ∀ i, (C i).IsActiveAt x' → (C i).a ⬝ᵥ d = 0 := by
      intro i hi
      have h1 : (C i).a ⬝ᵥ x' = (C i).b := hi
      rw [hdd, dotProduct_sub, hy0 i hi, h1, sub_self]
    -- Moving off `x'` along `d` stays feasible for small steps.
    have hev : ∀ᶠ ε : ℝ in nhds (0:ℝ), ∀ i, (C i).IsSatisfiedAt (x' + ε • d) := by
      rw [Filter.eventually_all]
      intro i
      by_cases hact : (C i).IsActiveAt x'
      · filter_upwards with ε
        have hval : (C i).a ⬝ᵥ (x' + ε • d) = (C i).b := by
          rw [dotProduct_add, dotProduct_smul, hdorth i hact, smul_zero, add_zero]
          exact hact
        rcases hr : (C i).rel with _ | _ | _ <;>
          simp only [LinearConstraint.IsSatisfiedAt, hr, hval] <;> norm_num
      · have hcont : Filter.Tendsto (fun ε : ℝ => (C i).a ⬝ᵥ (x' + ε • d)) (nhds 0)
            (nhds ((C i).a ⬝ᵥ x')) := by
          have : Continuous fun ε : ℝ => (C i).a ⬝ᵥ (x' + ε • d) := by
            simp only [dotProduct_add, dotProduct_smul, smul_eq_mul]
            exact continuous_const.add (continuous_id.mul continuous_const)
          have h0 := this.tendsto 0
          simpa using h0
        have hsat := hx i
        have hrel : (C i).rel ≠ ConstraintRel.eq := fun h => hact (heq_active i h)
        rcases hr : (C i).rel with _ | _ | _
        · -- ≥ : strict slack at x'
          simp only [LinearConstraint.IsSatisfiedAt, hr] at hsat
          have hlt : (C i).b < (C i).a ⬝ᵥ x' :=
            lt_of_le_of_ne hsat (fun h => hact h.symm)
          filter_upwards [hcont.eventually_const_le hlt] with ε hε
          simp only [LinearConstraint.IsSatisfiedAt, hr]
          exact hε
        · -- ≤ : strict slack at x'
          simp only [LinearConstraint.IsSatisfiedAt, hr] at hsat
          have hlt : (C i).a ⬝ᵥ x' < (C i).b :=
            lt_of_le_of_ne hsat (fun h => hact h)
          filter_upwards [hcont.eventually_le_const hlt] with ε hε
          simp only [LinearConstraint.IsSatisfiedAt, hr]
          exact hε
        · exact absurd hr hrel
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨r, hr, hball⟩ := hev
    have hεpos : (0:ℝ) < r / 2 := by linarith
    have hdist : ∀ t : ℝ, |t| = r / 2 → dist t (0:ℝ) < r := by
      intro t ht
      rw [Real.dist_eq, sub_zero, ht]; linarith
    have hplus : x' + (r/2) • d ∈ constraintSet C :=
      hball (hdist (r/2) (by rw [abs_of_pos hεpos]))
    have hminus : x' + (-(r/2)) • d ∈ constraintSet C :=
      hball (hdist (-(r/2)) (by rw [abs_neg, abs_of_pos hεpos]))
    -- `x'` is the midpoint of these two distinct feasible points
    have hmid : x' ∈ openSegment ℝ (x' + (r/2) • d) (x' + (-(r/2)) • d) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, neg_mul]
      ring
    have hcontra := hext.2 hplus hminus hmid
    have : (r/2) • d = 0 := by
      have := congrArg (fun z => z - x') hcontra
      simpa using this
    have : d = 0 := by
      rcases smul_eq_zero.mp this with h | h
      · exact absurd h (by positivity)
      · exact h
    exact hd0 this
  tfae_finish
end R6RayHelper1

/- Accepted Prove2Me helper ced37f90-ba52-47fe-9824-34ad96a43e5e, submission bf2088e6-ea9b-4b02-a219-55d535b01eaa, author MKPynnic. -/
section R6RayHelper2
open Matrix LinearOptimization


namespace LOCore

/-- The span of the constraint vectors active at `x`. -/
def activeSpan {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ((fun i => A i) '' {i | A i ⬝ᵥ x = b i})

lemma mem_polyhedron_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) : x ∈ polyhedron A b ↔ ∀ i, b i ≤ A i ⬝ᵥ x := by
  constructor
  · intro h i; exact h i
  · intro h i; exact h i

lemma constraintSet_generalForm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    constraintSet (generalFormSystem A b) = polyhedron A b := by
  ext x
  constructor
  · intro h i; exact h i
  · intro h i; exact h i

/-- Theorem 2.2, specialised to the general-form system at a feasible point:
the active vectors span iff the active system pins `x` down. -/
lemma activeSpan_top_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x : Fin n → ℝ) :
    activeSpan A b x = ⊤ ↔
      ∀ y : Fin n → ℝ, (∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ y = b i) → y = x :=
  (lp_active_constraint_equiv (generalFormSystem A b) x).out 1 2

/-- Theorem 2.2 again: spanning active vectors give a basic solution. -/
lemma isBasicSolution_of_activeSpan_top {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (x : Fin n → ℝ) (h : activeSpan A b x = ⊤) :
    IsBasicSolution (generalFormSystem A b) x := by
  refine ⟨fun i hi => absurd hi (by simp [generalFormSystem]), ?_⟩
  exact ((lp_active_constraint_equiv (generalFormSystem A b) x).out 1 0).mp h

/-- The rows of `A` span `ℝⁿ` iff only `0` is annihilated by all of them. -/
lemma rows_span_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    (∃ s : Finset (Fin m), s.card = n ∧ LinearIndependent ℝ (fun i : s => A i.1)) ↔
      ∀ y : Fin n → ℝ, (∀ i, A i ⬝ᵥ y = 0) → y = 0 := by
  have h := lp_active_constraint_equiv (fun i => (⟨A i, 0, .ge⟩ : LinearConstraint n)) 0
  have h02 := h.out 0 2
  constructor
  · intro hs
    intro y hy
    refine h02.mp ?_ y ?_
    · obtain ⟨s, hcard, hli⟩ := hs
      exact ⟨s, hcard, fun i _ => by show A i ⬝ᵥ (0 : Fin n → ℝ) = 0; simp, hli⟩
    · intro i _
      exact hy i
  · intro hy
    obtain ⟨s, hcard, -, hli⟩ := h02.mpr (fun y hy' => hy y (fun i => hy' i (by
      show A i ⬝ᵥ (0 : Fin n → ℝ) = 0; simp)))
    exact ⟨s, hcard, hli⟩

/-- Moving along a ray on which the cost strictly decreases makes the LP unbounded. -/
lemma unbounded_of_ray {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) {x e : Fin n → ℝ} (hx : x ∈ polyhedron A b)
    (hray : ∀ i, 0 ≤ A i ⬝ᵥ e) (hc : c ⬝ᵥ e < 0) :
    ∀ M : ℝ, ∃ w ∈ polyhedron A b, c ⬝ᵥ w < M := by
  intro M
  obtain ⟨lam, hlam0, hlam⟩ : ∃ lam : ℝ, 0 ≤ lam ∧ c ⬝ᵥ x + lam * (c ⬝ᵥ e) < M := by
    refine ⟨max 0 ((c ⬝ᵥ x - M) / (-(c ⬝ᵥ e)) + 1), le_max_left _ _, ?_⟩
    have hpos : 0 < -(c ⬝ᵥ e) := by linarith
    have hge : (c ⬝ᵥ x - M) / (-(c ⬝ᵥ e)) + 1 ≤ max 0 ((c ⬝ᵥ x - M) / (-(c ⬝ᵥ e)) + 1) :=
      le_max_right _ _
    have hkey : (c ⬝ᵥ x - M) < ((c ⬝ᵥ x - M) / (-(c ⬝ᵥ e)) + 1) * (-(c ⬝ᵥ e)) := by
      rw [add_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt hpos)]
      linarith
    nlinarith [hge, hpos]
  refine ⟨x + lam • e, ?_, ?_⟩
  · intro i
    have h1 : b i ≤ A i ⬝ᵥ x := hx i
    have h2 : 0 ≤ lam * (A i ⬝ᵥ e) := mul_nonneg hlam0 (hray i)
    show b i ≤ A i ⬝ᵥ (x + lam • e)
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    linarith
  · rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    exact hlam

/-- The blocking step: from a feasible `x` and a direction `e` that keeps every
active constraint active and is blocked by at least one constraint, we reach a
feasible point whose active constraints span strictly more. -/
lemma block {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {x e : Fin n → ℝ} (hx : x ∈ polyhedron A b)
    (hact : ∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ e = 0)
    (hS : (Finset.univ.filter (fun i => A i ⬝ᵥ e < 0)).Nonempty) :
    ∃ lam : ℝ, 0 ≤ lam ∧ (x + lam • e) ∈ polyhedron A b ∧
      activeSpan A b x < activeSpan A b (x + lam • e) := by
  classical
  set S : Finset (Fin m) := Finset.univ.filter (fun i => A i ⬝ᵥ e < 0) with hSdef
  have hmemS : ∀ i, i ∈ S ↔ A i ⬝ᵥ e < 0 := by
    intro i; simp [hSdef]
  set f : Fin m → ℝ := fun i => (A i ⬝ᵥ x - b i) / (-(A i ⬝ᵥ e)) with hf
  set lam : ℝ := S.inf' hS f with hlam
  have hlam0 : 0 ≤ lam := by
    refine Finset.le_inf' hS f ?_
    intro i hi
    have hneg : A i ⬝ᵥ e < 0 := (hmemS i).mp hi
    have h1 : b i ≤ A i ⬝ᵥ x := hx i
    exact div_nonneg (by linarith) (by linarith)
  obtain ⟨j, hjS, hjeq⟩ := Finset.exists_mem_eq_inf' hS f
  have hlamj : lam = f j := by rw [hlam]; exact hjeq
  have hjneg : A j ⬝ᵥ e < 0 := (hmemS j).mp hjS
  -- feasibility of the new point
  have hfeas : (x + lam • e) ∈ polyhedron A b := by
    intro i
    have h1 : b i ≤ A i ⬝ᵥ x := hx i
    show b i ≤ A i ⬝ᵥ (x + lam • e)
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
    rcases lt_or_ge (A i ⬝ᵥ e) 0 with hneg | hnonneg
    · have hi : i ∈ S := (hmemS i).mpr hneg
      have hle : lam ≤ f i := Finset.inf'_le f hi
      have hpos : 0 < -(A i ⬝ᵥ e) := by linarith
      have hne : -(A i ⬝ᵥ e) ≠ 0 := ne_of_gt hpos
      have hne2 : A i ⬝ᵥ e ≠ 0 := ne_of_lt hneg
      have hval : f i * (-(A i ⬝ᵥ e)) = A i ⬝ᵥ x - b i := by
        exact div_mul_cancel₀ _ hne
      have hmul : lam * (-(A i ⬝ᵥ e)) ≤ A i ⬝ᵥ x - b i := by
        calc lam * (-(A i ⬝ᵥ e)) ≤ f i * (-(A i ⬝ᵥ e)) :=
              mul_le_mul_of_nonneg_right hle (le_of_lt hpos)
          _ = A i ⬝ᵥ x - b i := hval
      linarith
    · nlinarith [mul_nonneg hlam0 hnonneg]
  -- previously active constraints stay active
  have hkeep : ∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ (x + lam • e) = b i := by
    intro i hi
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hact i hi, mul_zero, add_zero]
    exact hi
  -- the blocking constraint j becomes active
  have hjact : A j ⬝ᵥ (x + lam • e) = b j := by
    have hne : A j ⬝ᵥ e ≠ 0 := ne_of_lt hjneg
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hlamj]
    show A j ⬝ᵥ x + ((A j ⬝ᵥ x - b j) / (-(A j ⬝ᵥ e))) * (A j ⬝ᵥ e) = b j
    field_simp
    ring
  -- and its vector was not in the old span
  have hjnot : A j ∉ activeSpan A b x := by
    intro hmem
    have hsub : ((fun i => A i) '' {i | A i ⬝ᵥ x = b i}) ⊆
        {v : Fin n → ℝ | v ⬝ᵥ e = 0} := by
      rintro v ⟨i, hi, rfl⟩
      exact hact i hi
    have hspan : activeSpan A b x ≤
        (⟨⟨⟨{v : Fin n → ℝ | v ⬝ᵥ e = 0}, by
            intro u v hu hv
            simp only [Set.mem_setOf_eq, add_dotProduct] at *
            rw [hu, hv, add_zero]⟩, by simp⟩, by
            intro r v hv
            simp only [Set.mem_setOf_eq, smul_dotProduct] at *
            rw [hv, smul_zero]⟩ : Submodule ℝ (Fin n → ℝ)) :=
      Submodule.span_le.mpr hsub
    have : A j ⬝ᵥ e = 0 := hspan hmem
    linarith
  refine ⟨lam, hlam0, hfeas, lt_of_le_of_ne ?_ ?_⟩
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨i, hi, rfl⟩
    exact Submodule.subset_span ⟨i, hkeep i hi, rfl⟩
  · intro hEq
    exact hjnot (hEq ▸ Submodule.subset_span ⟨j, hjact, rfl⟩)



/-- **Descent to a basic feasible solution.** If the rows of `A` span `ℝⁿ` (equivalently,
`P` contains no line), then from any feasible point we can reach a basic feasible solution
of no greater cost — unless the cost is unbounded below on `P`. -/
lemma descent {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hspan : ∀ y : Fin n → ℝ, (∀ i, A i ⬝ᵥ y = 0) → y = 0) :
    ∀ (k : ℕ) (x : Fin n → ℝ), x ∈ polyhedron A b →
      n - Module.finrank ℝ (activeSpan A b x) ≤ k →
      (∀ M : ℝ, ∃ w ∈ polyhedron A b, c ⬝ᵥ w < M) ∨
      (∃ y, IsBasicFeasibleSolution (generalFormSystem A b) y ∧ c ⬝ᵥ y ≤ c ⬝ᵥ x) := by
  classical
  have hfrn : Module.finrank ℝ (Fin n → ℝ) = n := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  have hbfs : ∀ z : Fin n → ℝ, z ∈ polyhedron A b → activeSpan A b z = ⊤ →
      IsBasicFeasibleSolution (generalFormSystem A b) z := by
    intro z hz htop
    exact ⟨isBasicSolution_of_activeSpan_top A b z htop, by
      rw [constraintSet_generalForm]; exact hz⟩
  intro k
  induction k with
  | zero =>
      intro x hx hk
      right
      have hle : Module.finrank ℝ (activeSpan A b x) ≤ n := by
        have h := Submodule.finrank_le (activeSpan A b x)
        rw [hfrn] at h
        exact h
      have heq : Module.finrank ℝ (activeSpan A b x) = Module.finrank ℝ (Fin n → ℝ) := by
        rw [hfrn]; omega
      exact ⟨x, hbfs x hx (Submodule.eq_top_of_finrank_eq heq), le_refl _⟩
  | succ k ih =>
      intro x hx hk
      by_cases htop : activeSpan A b x = ⊤
      · exact Or.inr ⟨x, hbfs x hx htop, le_refl _⟩
      -- a direction along which every active constraint stays active
      obtain ⟨y0, hy0, hy0ne⟩ : ∃ y : Fin n → ℝ,
          (∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ y = b i) ∧ y ≠ x := by
        by_contra hcon
        push_neg at hcon
        exact htop ((activeSpan_top_iff A b x).mpr (fun y hy => hcon y hy))
      set d : Fin n → ℝ := y0 - x with hd
      have hdne : d ≠ 0 := sub_ne_zero.mpr hy0ne
      have hdact : ∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ d = 0 := by
        intro i hi
        rw [hd, dotProduct_sub, hy0 i hi, hi, sub_self]
      obtain ⟨i₀, hi₀⟩ : ∃ i, A i ⬝ᵥ d ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hdne (hspan d hcon)
      -- one descent step, given a usable direction
      have step : ∀ e : Fin n → ℝ, (∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ e = 0) →
          (Finset.univ.filter (fun i => A i ⬝ᵥ e < 0)).Nonempty → c ⬝ᵥ e ≤ 0 →
          (∀ M : ℝ, ∃ w ∈ polyhedron A b, c ⬝ᵥ w < M) ∨
          (∃ y, IsBasicFeasibleSolution (generalFormSystem A b) y ∧ c ⬝ᵥ y ≤ c ⬝ᵥ x) := by
        intro e hacte hSe hce
        obtain ⟨lam, hlam0, hfeas, hlt⟩ := block A b hx hacte hSe
        have hrank : Module.finrank ℝ (activeSpan A b x) <
            Module.finrank ℝ (activeSpan A b (x + lam • e)) :=
          Submodule.finrank_lt_finrank_of_lt hlt
        have hk' : n - Module.finrank ℝ (activeSpan A b (x + lam • e)) ≤ k := by omega
        rcases ih (x + lam • e) hfeas hk' with h | ⟨y, hy, hcy⟩
        · exact Or.inl h
        · refine Or.inr ⟨y, hy, ?_⟩
          have hmono : c ⬝ᵥ (x + lam • e) ≤ c ⬝ᵥ x := by
            rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
            have : lam * (c ⬝ᵥ e) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam0 hce
            linarith
          linarith
      -- unboundedness when the ray is never blocked
      have ray : ∀ e : Fin n → ℝ, ¬ (Finset.univ.filter (fun i => A i ⬝ᵥ e < 0)).Nonempty →
          ∀ i, 0 ≤ A i ⬝ᵥ e := by
        intro e hSe i
        by_contra hcon
        push_neg at hcon
        exact hSe ⟨i, by simp [hcon]⟩
      have hnegdot : ∀ (v : Fin n → ℝ) (i : Fin m), A i ⬝ᵥ (-v) = -(A i ⬝ᵥ v) := by
        intro v i; rw [dotProduct_neg]
      have hdactneg : ∀ i, A i ⬝ᵥ x = b i → A i ⬝ᵥ (-d) = 0 := by
        intro i hi; rw [hnegdot, hdact i hi, neg_zero]
      rcases lt_trichotomy (c ⬝ᵥ d) 0 with hc | hc | hc
      · by_cases hS : (Finset.univ.filter (fun i => A i ⬝ᵥ d < 0)).Nonempty
        · exact step d hdact hS (le_of_lt hc)
        · exact Or.inl (unbounded_of_ray A b c hx (ray d hS) hc)
      · -- the cost is flat along `d`; move in whichever direction is blocked
        rcases lt_or_gt_of_ne hi₀ with hlt | hgt
        · refine step d hdact ⟨i₀, by simp [hlt]⟩ (le_of_eq hc)
        · refine step (-d) hdactneg ⟨i₀, by simp [hnegdot, hgt]⟩ ?_
          rw [dotProduct_neg, hc, neg_zero]
      · have hcneg : c ⬝ᵥ (-d) < 0 := by rw [dotProduct_neg]; linarith
        by_cases hS : (Finset.univ.filter (fun i => A i ⬝ᵥ (-d) < 0)).Nonempty
        · exact step (-d) hdactneg hS (le_of_lt hcneg)
        · exact Or.inl (unbounded_of_ray A b c hx (ray (-d) hS) hcneg)

end LOCore


open LOCore

theorem LinearOptimization.polyhedron_extreme_point_existence {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hne : (polyhedron A b).Nonempty) :
    List.TFAE
      [ (Set.extremePoints ℝ (polyhedron A b)).Nonempty,
        ¬ ContainsLine (polyhedron A b),
        ∃ s : Finset (Fin m), s.card = n ∧
          LinearIndependent ℝ (fun i : s => A i.1) ] := by
  classical
  obtain ⟨x₀, hx₀⟩ := hne
  -- A polyhedron contains a line exactly when some nonzero direction is killed by every row.
  have hline : ContainsLine (polyhedron A b) ↔ ∃ d : Fin n → ℝ, d ≠ 0 ∧ ∀ i, A i ⬝ᵥ d = 0 := by
    constructor
    · rintro ⟨z, hz, d, hd0, hd⟩
      refine ⟨d, hd0, fun i => ?_⟩
      by_contra hcon
      -- pick a scalar driving the `i`-th constraint below its bound
      obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, A i ⬝ᵥ z + lam * (A i ⬝ᵥ d) < b i := by
        rcases lt_or_gt_of_ne hcon with h | h
        · refine ⟨(b i - 1 - A i ⬝ᵥ z) / (A i ⬝ᵥ d), ?_⟩
          rw [div_mul_cancel₀ _ (ne_of_lt h)]; linarith
        · refine ⟨(b i - 1 - A i ⬝ᵥ z) / (A i ⬝ᵥ d), ?_⟩
          rw [div_mul_cancel₀ _ (ne_of_gt h)]; linarith
      have hmem : b i ≤ A i ⬝ᵥ (z + lam • d) := hd lam i
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul] at hmem
      linarith
    · rintro ⟨d, hd0, hd⟩
      refine ⟨x₀, hx₀, d, hd0, fun lam i => ?_⟩
      have h1 : b i ≤ A i ⬝ᵥ x₀ := hx₀ i
      show b i ≤ A i ⬝ᵥ (x₀ + lam • d)
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hd i, mul_zero, add_zero]
      exact h1
  have hspan_iff : (¬ ContainsLine (polyhedron A b)) ↔
      ∀ y : Fin n → ℝ, (∀ i, A i ⬝ᵥ y = 0) → y = 0 := by
    rw [hline]
    constructor
    · intro h y hy
      by_contra hy0
      exact h ⟨y, hy0, hy⟩
    · rintro h ⟨d, hd0, hd⟩
      exact hd0 (h d hd)
  tfae_have 1 → 2 := by
    rintro ⟨x, hx⟩
    rw [hspan_iff]
    intro y hy
    by_contra hy0
    -- `x ± y` are both feasible and `x` is their midpoint
    have hfeas : ∀ t : ℝ, x + t • y ∈ polyhedron A b := by
      intro t i
      have h1 : b i ≤ A i ⬝ᵥ x := hx.1 i
      show b i ≤ A i ⬝ᵥ (x + t • y)
      rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hy i, mul_zero, add_zero]
      exact h1
    have hmid : x ∈ openSegment ℝ (x + (1:ℝ) • y) (x + (-1:ℝ) • y) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have := hx.2 (hfeas 1) (hfeas (-1)) hmid
    have hy1 : (1:ℝ) • y = 0 := by
      have := congrArg (fun z => z - x) this
      simpa using this
    exact hy0 (by simpa using hy1)
  tfae_have 2 → 3 := by
    intro h2
    exact (rows_span_iff A).mpr (hspan_iff.mp h2)
  tfae_have 3 → 2 := by
    intro h3
    exact hspan_iff.mpr ((rows_span_iff A).mp h3)
  tfae_have 3 → 1 := by
    intro h3
    have hspan := (rows_span_iff A).mp h3
    have hd := descent A b 0 hspan n x₀ hx₀ (Nat.sub_le _ _)
    rcases hd with hunb | ⟨y, hy, -⟩
    · exfalso
      obtain ⟨w, -, hw⟩ := hunb 0
      rw [zero_dotProduct] at hw
      exact lt_irrefl _ hw
    · refine ⟨y, ?_⟩
      have hymem : y ∈ constraintSet (generalFormSystem A b) := hy.2
      have hnec : (constraintSet (generalFormSystem A b)).Nonempty := ⟨y, hymem⟩
      have hthm := lp_vertex_extreme_bfs_equiv (generalFormSystem A b) y hnec hymem
      have := (hthm.out 2 1).mp hy
      rwa [constraintSet_generalForm] at this
  tfae_finish
end R6RayHelper2

/- Accepted Prove2Me helper 22c841fa-457e-4343-b7ae-f4482f04b352, submission 09c151b8-eb7d-431d-9bd9-546b5012efa0, author Harry_Xu. -/
section R6RayHelper3
open Matrix

theorem LinearOptimization.cone_pointed_iff_extreme_zero {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) :
    (LinearOptimization.IsPointedCone (LinearOptimization.polyhedron A 0) ↔
      ¬ LinearOptimization.ContainsLine (LinearOptimization.polyhedron A 0)) ∧
    (¬ LinearOptimization.ContainsLine (LinearOptimization.polyhedron A 0) ↔
      ∃ s : Finset (Fin m), s.card = n ∧
        LinearIndependent ℝ (fun i : s ↦ A i.1)) := by
  classical
  have hzero : (0 : Fin n → ℝ) ∈ LinearOptimization.polyhedron A 0 := by
    intro i
    simp [LinearOptimization.polyhedron]
  have ht := LinearOptimization.polyhedron_extreme_point_existence A 0 ⟨0, hzero⟩
  have hfirst :
      LinearOptimization.IsPointedCone (LinearOptimization.polyhedron A 0) ↔
        ¬ LinearOptimization.ContainsLine (LinearOptimization.polyhedron A 0) := by
    constructor
    · intro hpoint
      apply (ht.out 0 1).mp
      refine ⟨0, ?_⟩
      simpa [LinearOptimization.IsPointedCone] using hpoint
    · intro hnoline
      obtain ⟨y, hy⟩ := (ht.out 1 0).mp hnoline
      have hyzero : y = 0 := by
        have htwo : (2 : ℝ) • y ∈ LinearOptimization.polyhedron A 0 := by
          intro i
          have hyi : 0 ≤ A i ⬝ᵥ y := hy.1 i
          change 0 ≤ A i ⬝ᵥ ((2 : ℝ) • y)
          rw [dotProduct_smul, smul_eq_mul]
          exact mul_nonneg (by norm_num) hyi
        have hmid : y ∈ openSegment ℝ (0 : Fin n → ℝ) ((2 : ℝ) • y) := by
          refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
          ext j
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
          ring
        exact (hy.2 hzero htwo hmid).symm
      subst y
      simpa [LinearOptimization.IsPointedCone] using hy
  exact ⟨hfirst, ht.out 1 2⟩
end R6RayHelper3

/- Accepted Prove2Me helper 4579e545-4dc9-4d40-9c94-5cc47f443ced, submission c840dfef-af8d-4699-b6c2-0383dcc3db7c, author Harry_Xu. -/
section R6RayHelper4
open Matrix

private lemma r6ray_4_extreme_nonempty_of_no_line_fintype
    {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (a : ι → (Fin n → ℝ)) (b : ι → ℝ)
    (hne : ({y | ∀ i, b i ≤ a i ⬝ᵥ y} : Set (Fin n → ℝ)).Nonempty)
    (hnoline : ¬ LinearOptimization.ContainsLine
      ({y | ∀ i, b i ≤ a i ⬝ᵥ y} : Set (Fin n → ℝ))) :
    (Set.extremePoints ℝ
      ({y | ∀ i, b i ≤ a i ⬝ᵥ y} : Set (Fin n → ℝ))).Nonempty := by
  classical
  let e := Fintype.equivFin ι
  let A : Matrix (Fin (Fintype.card ι)) (Fin n) ℝ := fun k ↦ a (e.symm k)
  let rhs : Fin (Fintype.card ι) → ℝ := fun k ↦ b (e.symm k)
  have hset : LinearOptimization.polyhedron A rhs =
      ({y | ∀ i, b i ≤ a i ⬝ᵥ y} : Set (Fin n → ℝ)) := by
    ext y
    constructor
    · intro hy i
      have hi := hy (e i)
      simpa [A, rhs, Matrix.mulVec] using hi
    · intro hy k
      simpa [A, rhs, Matrix.mulVec] using hy (e.symm k)
  have hne' : (LinearOptimization.polyhedron A rhs).Nonempty := by
    simpa [hset] using hne
  have hnoline' : ¬ LinearOptimization.ContainsLine
      (LinearOptimization.polyhedron A rhs) := by
    simpa [hset] using hnoline
  have ht := LinearOptimization.polyhedron_extreme_point_existence A rhs hne'
  obtain ⟨y, hy⟩ := (ht.out 1 0).mp hnoline'
  refine ⟨y, ?_⟩
  simpa [hset] using hy

private lemma r6ray_4_cone_value_bot_iff_exists_negative {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) :
    LinearOptimization.lpValue c (LinearOptimization.polyhedron A 0) = ⊥ ↔
      ∃ x ∈ LinearOptimization.polyhedron A 0, c ⬝ᵥ x < 0 := by
  classical
  constructor
  · intro hbot
    rw [LinearOptimization.lpValue, iInf_eq_bot] at hbot
    obtain ⟨x, hx⟩ := hbot ((-1 : ℝ) : EReal) (EReal.bot_lt_coe _)
    have hxmem : x ∈ LinearOptimization.polyhedron A 0 := by
      by_contra hnot
      simp [hnot] at hx
    refine ⟨x, hxmem, ?_⟩
    have hcost : c ⬝ᵥ x < -1 := by
      apply EReal.coe_lt_coe_iff.mp
      simpa [hxmem] using hx
    linarith
  · rintro ⟨d, hd, hcd⟩
    rw [LinearOptimization.lpValue, iInf_eq_bot]
    intro z hz
    induction z using EReal.rec with
    | bot => exact (lt_irrefl _ hz).elim
    | coe r =>
        let lam : ℝ := max 0 ((-r + 1) / (-(c ⬝ᵥ d)))
        have hden : 0 < -(c ⬝ᵥ d) := by linarith
        have hlam : 0 ≤ lam := le_max_left _ _
        have hge : (-r + 1) / (-(c ⬝ᵥ d)) ≤ lam := le_max_right _ _
        have hkey : -r + 1 ≤ lam * (-(c ⬝ᵥ d)) := by
          calc
            -r + 1 = ((-r + 1) / (-(c ⬝ᵥ d))) * (-(c ⬝ᵥ d)) := by
              rw [div_mul_cancel₀ _ (ne_of_gt hden)]
            _ ≤ lam * (-(c ⬝ᵥ d)) :=
              mul_le_mul_of_nonneg_right hge (le_of_lt hden)
        have hfeas : lam • d ∈ LinearOptimization.polyhedron A 0 := by
          intro i
          have hdi : 0 ≤ A i ⬝ᵥ d := hd i
          change 0 ≤ A i ⬝ᵥ (lam • d)
          rw [dotProduct_smul, smul_eq_mul]
          exact mul_nonneg hlam hdi
        refine ⟨lam • d, ?_⟩
        have hcost : c ⬝ᵥ (lam • d) < r := by
          rw [dotProduct_smul, smul_eq_mul]
          linarith
        simpa [hfeas] using EReal.coe_lt_coe_iff.mpr hcost
    | top =>
        have hzero : (0 : Fin n → ℝ) ∈ LinearOptimization.polyhedron A 0 := by
          intro i
          simp
        refine ⟨0, ?_⟩
        simpa [hzero] using EReal.coe_lt_top (0 : ℝ)

private lemma r6ray_4_extreme_normalized_slice_is_ray {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ) (d : Fin n → ℝ)
    (hd : d ∈ LinearOptimization.polyhedron A 0) (hcost : c ⬝ᵥ d = -1)
    (hext : d ∈ Set.extremePoints ℝ
      ({y | y ∈ LinearOptimization.polyhedron A 0 ∧ c ⬝ᵥ y = -1} :
        Set (Fin n → ℝ))) :
    LinearOptimization.IsExtremeRay A d := by
  classical
  let C : Option (Fin m) → LinearOptimization.LinearConstraint n
    | none => ⟨c, -1, .eq⟩
    | some i => ⟨A i, 0, .ge⟩
  have hCset : LinearOptimization.constraintSet C =
      ({y | y ∈ LinearOptimization.polyhedron A 0 ∧ c ⬝ᵥ y = -1} :
        Set (Fin n → ℝ)) := by
    ext y
    constructor
    · intro hy
      constructor
      · intro i
        have hi := hy (some i)
        have hi' : 0 ≤ A i ⬝ᵥ y := by
          simpa [C, LinearOptimization.LinearConstraint.IsSatisfiedAt] using hi
        exact hi'
      · have hnone := hy none
        simpa [C, LinearOptimization.LinearConstraint.IsSatisfiedAt] using hnone
    · rintro ⟨hy, hcy⟩ o
      cases o with
      | none => simpa [C, LinearOptimization.LinearConstraint.IsSatisfiedAt] using hcy
      | some i =>
          have hi' : 0 ≤ A i ⬝ᵥ y := hy i
          simpa [C, LinearOptimization.LinearConstraint.IsSatisfiedAt] using hi'
  have hdC : d ∈ LinearOptimization.constraintSet C := by
    rw [hCset]
    exact ⟨hd, hcost⟩
  have hextC : d ∈ Set.extremePoints ℝ (LinearOptimization.constraintSet C) := by
    rw [hCset]
    exact hext
  have ht := LinearOptimization.lp_vertex_extreme_bfs_equiv C d ⟨d, hdC⟩ hdC
  have hbfs := (ht.out 1 2).mp hextC
  obtain ⟨heqactive, s, hcard, hactive, hli⟩ := hbfs.1
  have hnoneMem : none ∈ s := by
    by_contra hnone
    let K : Submodule ℝ (Fin n → ℝ) := {
      carrier := {v | v ⬝ᵥ d = 0}
      zero_mem' := by simp
      add_mem' := by
        intro u v hu hv
        change u ⬝ᵥ d = 0 at hu
        change v ⬝ᵥ d = 0 at hv
        change (u + v) ⬝ᵥ d = 0
        rw [add_dotProduct, hu, hv, add_zero]
      smul_mem' := by
        intro r v hv
        change v ⬝ᵥ d = 0 at hv
        change (r • v) ⬝ᵥ d = 0
        rw [smul_dotProduct, hv, smul_zero] }
    have hrange : Set.range (fun i : s ↦ (C i.1).a) ⊆ K := by
      rintro v ⟨i, rfl⟩
      have hi := hactive i.1 i.2
      cases hidx : i.1 with
      | none =>
          exfalso
          exact hnone (by simpa [hidx] using i.2)
      | some j =>
          simpa [K, C, hidx, LinearOptimization.LinearConstraint.IsActiveAt] using hi
    have hspan : Submodule.span ℝ (Set.range (fun i : s ↦ (C i.1).a)) = ⊤ := by
      apply hli.span_eq_top_of_card_eq_finrank'
      simpa [hcard, Module.finrank_pi ℝ]
    have htopK : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ K := by
      rw [← hspan]
      exact Submodule.span_le.mpr hrange
    have hdd : d ⬝ᵥ d = 0 := htopK (Submodule.mem_top)
    have hdzero : d = 0 := by
      ext j
      change d j = 0
      have hsquares : (∑ k : Fin n, d k * d k) = 0 := by
        simpa [dotProduct] using hdd
      have hle : d j * d j ≤ ∑ k : Fin n, d k * d k :=
        Finset.single_le_sum (fun k hk ↦ mul_self_nonneg (d k)) (Finset.mem_univ j)
      nlinarith [mul_self_nonneg (d j)]
    rw [hdzero, dotProduct_zero] at hcost
    norm_num at hcost
  let t : Finset (Fin m) := Finset.univ.filter (fun i ↦ some i ∈ s)
  let eFun : t → (s.erase none) := fun i ↦ ⟨some i.1, by
    simp only [Finset.mem_erase]
    have hi := i.2
    simp only [t, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact ⟨Option.some_ne_none _, hi⟩⟩
  have heFun : Function.Bijective eFun := by
    constructor
    · intro i j hij
      apply Subtype.ext
      have := congrArg (fun o : Option (Fin m) ↦ o) (congrArg Subtype.val hij)
      simpa [eFun] using this
    · intro o
      cases hidx : o.1 with
      | none =>
          have hone : o.1 ≠ none := (Finset.mem_erase.mp o.2).1
          exact (hone hidx).elim
      | some i =>
          have his0 := (Finset.mem_erase.mp o.2).2
          have his : some i ∈ s := by simpa [hidx] using his0
          let ii : t := ⟨i, by simp [t, his]⟩
          refine ⟨ii, ?_⟩
          apply Subtype.ext
          simp [eFun, ii, hidx]
  let e : t ≃ (s.erase none) := Equiv.ofBijective eFun heFun
  have hcardt : t.card = n - 1 := by
    have hc := Fintype.card_congr e
    simp only [Fintype.card_coe] at hc
    rw [Finset.card_erase_of_mem hnoneMem, hcard] at hc
    exact hc
  have hliErase : LinearIndependent ℝ
      (fun i : (s.erase none) ↦ (C i.1).a) := by
    apply hli.comp (fun i : (s.erase none) ↦
      (⟨i.1, Finset.mem_of_mem_erase i.2⟩ : s))
    intro i j hij
    apply Subtype.ext
    exact congrArg (fun z : s ↦ z.1) hij
  have hliT : LinearIndependent ℝ (fun i : t ↦ A i.1) := by
    have hcomp := hliErase.comp e e.injective
    simpa [e, eFun, C, Function.comp_def] using hcomp
  refine ⟨hd, ?_, t, hcardt, ?_, hliT⟩
  · intro hdzero
    rw [hdzero, dotProduct_zero] at hcost
    norm_num at hcost
  · intro i hi
    have his : some i ∈ s := by
      simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using hi
    have hact := hactive (some i) his
    simpa [C, LinearOptimization.LinearConstraint.IsActiveAt] using hact

theorem LinearOptimization.cone_unbounded_iff_extreme_ray {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (hpointed : LinearOptimization.IsPointedCone
      (LinearOptimization.polyhedron A 0)) :
    LinearOptimization.lpValue c (LinearOptimization.polyhedron A 0) = ⊥ ↔
      ∃ d : Fin n → ℝ,
        LinearOptimization.IsExtremeRay A d ∧ c ⬝ᵥ d < 0 := by
  classical
  rw [r6ray_4_cone_value_bot_iff_exists_negative]
  constructor
  · rintro ⟨x, hx, hcx⟩
    let alpha : ℝ := (-1) / (c ⬝ᵥ x)
    have halpha : 0 < alpha := div_pos_of_neg_of_neg (by norm_num) hcx
    let xnorm : Fin n → ℝ := alpha • x
    have hxnorm : xnorm ∈ LinearOptimization.polyhedron A 0 := by
      intro i
      have hxi : 0 ≤ A i ⬝ᵥ x := hx i
      change 0 ≤ A i ⬝ᵥ (alpha • x)
      rw [dotProduct_smul, smul_eq_mul]
      exact mul_nonneg (le_of_lt halpha) hxi
    have hcostnorm : c ⬝ᵥ xnorm = -1 := by
      rw [show xnorm = alpha • x by rfl, dotProduct_smul, smul_eq_mul]
      exact div_mul_cancel₀ (-1) (ne_of_lt hcx)
    let B : ((Fin m) ⊕ Bool) → (Fin n → ℝ)
      | Sum.inl i => A i
      | Sum.inr false => c
      | Sum.inr true => -c
    let rhs : ((Fin m) ⊕ Bool) → ℝ
      | Sum.inl _ => 0
      | Sum.inr false => -1
      | Sum.inr true => 1
    have hBset : ({y | ∀ q, rhs q ≤ B q ⬝ᵥ y} : Set (Fin n → ℝ)) =
        ({y | y ∈ LinearOptimization.polyhedron A 0 ∧ c ⬝ᵥ y = -1} :
          Set (Fin n → ℝ)) := by
      ext y
      constructor
      · intro hy
        constructor
        · intro i
          have hi' : 0 ≤ A i ⬝ᵥ y := by simpa [B, rhs] using hy (Sum.inl i)
          exact hi'
        · have hlo := hy (Sum.inr false)
          have hhi := hy (Sum.inr true)
          simp [B, rhs, dotProduct] at hlo hhi
          change c ⬝ᵥ y = -1
          rw [dotProduct]
          linarith
      · rintro ⟨hy, hcy⟩ q
        rcases q with i | s
        · have hi' : 0 ≤ A i ⬝ᵥ y := hy i
          simpa [B, rhs] using hi'
        · cases s with
          | false =>
              change -1 ≤ c ⬝ᵥ y
              linarith
          | true =>
              change 1 ≤ (-c) ⬝ᵥ y
              have hcy' : (∑ i : Fin n, c i * y i) = -1 := by
                simpa [dotProduct] using hcy
              simp only [dotProduct, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
              linarith
    have hneB : ({y | ∀ q, rhs q ≤ B q ⬝ᵥ y} :
        Set (Fin n → ℝ)).Nonempty := by
      rw [hBset]
      exact ⟨xnorm, hxnorm, hcostnorm⟩
    have hnolineCone : ¬ LinearOptimization.ContainsLine
        (LinearOptimization.polyhedron A 0) :=
      (LinearOptimization.cone_pointed_iff_extreme_zero A).1.mp hpointed
    have hnolineB : ¬ LinearOptimization.ContainsLine
        ({y | ∀ q, rhs q ≤ B q ⬝ᵥ y} : Set (Fin n → ℝ)) := by
      intro hline
      apply hnolineCone
      rcases hline with ⟨y, hy, d, hdne, hline⟩
      have hySlice : y ∈
          ({z | z ∈ LinearOptimization.polyhedron A 0 ∧ c ⬝ᵥ z = -1} :
            Set (Fin n → ℝ)) := by
        rw [← hBset]
        exact hy
      have hy' : y ∈ LinearOptimization.polyhedron A 0 := hySlice.1
      refine ⟨y, hy', d, hdne, ?_⟩
      intro lam
      have hlamSlice : y + lam • d ∈
          ({z | z ∈ LinearOptimization.polyhedron A 0 ∧ c ⬝ᵥ z = -1} :
            Set (Fin n → ℝ)) := by
        rw [← hBset]
        exact hline lam
      exact hlamSlice.1
    obtain ⟨d, hdext⟩ := r6ray_4_extreme_nonempty_of_no_line_fintype B rhs hneB hnolineB
    have hdext' : d ∈ Set.extremePoints ℝ
        ({y | y ∈ LinearOptimization.polyhedron A 0 ∧ c ⬝ᵥ y = -1} :
          Set (Fin n → ℝ)) := by
      rw [← hBset]
      exact hdext
    have hdslice := hdext'.1
    refine ⟨d, r6ray_4_extreme_normalized_slice_is_ray A c d hdslice.1 hdslice.2 hdext', ?_⟩
    have hcd : c ⬝ᵥ d = -1 := hdslice.2
    linarith
  · rintro ⟨d, hd, hcd⟩
    exact ⟨d, hd.1, hcd⟩
end R6RayHelper4

/- Accepted Prove2Me helper 6b5826b9-0201-4cbe-aa9b-d4334975d880, submission 1bfac9d7-cab2-4b56-921f-a2a83723cd2b, author Harry_Xu. -/
section R6RayHelper5
open Matrix Finset

theorem LinearOptimization.fourier_motzkin_projection {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (b : Fin m → ℝ) :
    LinearOptimization.fourierMotzkinEliminate A b =
      (fun x : Fin (n + 1) → ℝ => fun l : Fin n => x l.castSucc) ''
        LinearOptimization.polyhedron A b := by
  classical
  ext y
  constructor
  · intro hy
    let pos : Finset (Fin m) :=
      Finset.univ.filter (fun i => 0 < A i (Fin.last n))
    let neg : Finset (Fin m) :=
      Finset.univ.filter (fun i => A i (Fin.last n) < 0)
    by_cases hp : pos.Nonempty
    · obtain ⟨i, hi, hiMax⟩ :=
        Finset.exists_max_image pos
          (fun r => LinearOptimization.fourierMotzkinBound A b r y) hp
      have hai : 0 < A i (Fin.last n) := (Finset.mem_filter.mp hi).2
      refine ⟨Fin.snoc y (LinearOptimization.fourierMotzkinBound A b i y), ?_, ?_⟩
      · intro r
        change b r ≤ ∑ q : Fin (n + 1), A r q *
          (Fin.snoc y (LinearOptimization.fourierMotzkinBound A b i y) :
            Fin (n + 1) → ℝ) q
        rw [Fin.sum_univ_castSucc]
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        simp only [LinearOptimization.fourierMotzkinBound]
        by_cases har : 0 < A r (Fin.last n)
        · have hr : r ∈ pos := Finset.mem_filter.mpr ⟨Finset.mem_univ r, har⟩
          have hbound := hiMax r hr
          simp only [LinearOptimization.fourierMotzkinBound] at hbound
          rw [div_le_iff₀ har] at hbound
          nlinarith
        · by_cases har0 : A r (Fin.last n) = 0
          · have hzero := hy.1 r har0
            simp only [har0, zero_mul, add_zero]
            exact hzero
          · have harneg : A r (Fin.last n) < 0 :=
              lt_of_le_of_ne (le_of_not_gt har) har0
            have hbound := hy.2 i r hai harneg
            simp only [LinearOptimization.fourierMotzkinBound] at hbound
            rw [le_div_iff_of_neg harneg] at hbound
            nlinarith
      · funext l
        simp
    · by_cases hn : neg.Nonempty
      · obtain ⟨j, hj, hjMin⟩ :=
          Finset.exists_min_image neg
            (fun r => LinearOptimization.fourierMotzkinBound A b r y) hn
        have haj : A j (Fin.last n) < 0 := (Finset.mem_filter.mp hj).2
        refine ⟨Fin.snoc y (LinearOptimization.fourierMotzkinBound A b j y), ?_, ?_⟩
        · intro r
          change b r ≤ ∑ q : Fin (n + 1), A r q *
            (Fin.snoc y (LinearOptimization.fourierMotzkinBound A b j y) :
              Fin (n + 1) → ℝ) q
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          simp only [LinearOptimization.fourierMotzkinBound]
          by_cases har : 0 < A r (Fin.last n)
          · exact (hp ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, har⟩⟩).elim
          · by_cases har0 : A r (Fin.last n) = 0
            · have hzero := hy.1 r har0
              simp only [har0, zero_mul, add_zero]
              exact hzero
            · have harneg : A r (Fin.last n) < 0 :=
                lt_of_le_of_ne (le_of_not_gt har) har0
              have hr : r ∈ neg := Finset.mem_filter.mpr ⟨Finset.mem_univ r, harneg⟩
              have hbound := hjMin r hr
              simp only [LinearOptimization.fourierMotzkinBound] at hbound
              rw [le_div_iff_of_neg harneg] at hbound
              nlinarith
        · funext l
          simp
      · refine ⟨Fin.snoc y 0, ?_, ?_⟩
        · intro r
          change b r ≤ ∑ q : Fin (n + 1), A r q *
            (Fin.snoc y 0 : Fin (n + 1) → ℝ) q
          rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last, mul_zero, add_zero]
          have hnotpos : ¬ 0 < A r (Fin.last n) := by
            intro har
            exact hp ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, har⟩⟩
          have hnotneg : ¬ A r (Fin.last n) < 0 := by
            intro har
            exact hn ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_univ r, har⟩⟩
          have har0 : A r (Fin.last n) = 0 :=
            le_antisymm (le_of_not_gt hnotpos) (le_of_not_gt hnotneg)
          exact hy.1 r har0
        · funext l
          simp
  · rintro ⟨x, hx, rfl⟩
    constructor
    · intro k hk
      have h := hx k
      change b k ≤ ∑ q : Fin (n + 1), A k q * x q at h
      rw [Fin.sum_univ_castSucc] at h
      simpa [hk] using h
    · intro i j hi hj
      have hfi := hx i
      have hfj := hx j
      change b i ≤ ∑ q : Fin (n + 1), A i q * x q at hfi
      change b j ≤ ∑ q : Fin (n + 1), A j q * x q at hfj
      rw [Fin.sum_univ_castSucc] at hfi hfj
      have hLower :
          LinearOptimization.fourierMotzkinBound A b i
              (fun l : Fin n => x l.castSucc) ≤ x (Fin.last n) := by
        simp only [LinearOptimization.fourierMotzkinBound]
        rw [div_le_iff₀ hi]
        linarith
      have hUpper :
          x (Fin.last n) ≤ LinearOptimization.fourierMotzkinBound A b j
              (fun l : Fin n => x l.castSucc) := by
        simp only [LinearOptimization.fourierMotzkinBound]
        rw [le_div_iff_of_neg hj]
        linarith
      exact hLower.trans hUpper
end R6RayHelper5

/- Accepted Prove2Me helper 6df0cbfd-26b3-4e0b-9e6e-bc8b4cc5ee5b, submission 3e5da8f3-b572-4e6c-963c-7c80dbd62846, author Harry_Xu. -/
section R6RayHelper6
open Matrix Finset

theorem LinearOptimization.fourier_motzkin_eliminate_is_polyhedron {m n : ℕ}
    (A : Matrix (Fin m) (Fin (n + 1)) ℝ) (b : Fin m → ℝ) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      LinearOptimization.fourierMotzkinEliminate A b =
        LinearOptimization.polyhedron A' b' := by
  classical
  let Z := {i : Fin m // A i (Fin.last n) = 0}
  let P := {i : Fin m // 0 < A i (Fin.last n)}
  let N := {i : Fin m // A i (Fin.last n) < 0}
  let I := Z ⊕ (P × N)
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let A' : Matrix (Fin (Fintype.card I)) (Fin n) ℝ := fun r l =>
    match e r with
    | Sum.inl k => A k.1 l.castSucc
    | Sum.inr ij =>
        A ij.1.1 l.castSucc / A ij.1.1 (Fin.last n) -
          A ij.2.1 l.castSucc / A ij.2.1 (Fin.last n)
  let b' : Fin (Fintype.card I) → ℝ := fun r =>
    match e r with
    | Sum.inl k => b k.1
    | Sum.inr ij =>
        b ij.1.1 / A ij.1.1 (Fin.last n) -
          b ij.2.1 / A ij.2.1 (Fin.last n)
  refine ⟨Fintype.card I, A', b', ?_⟩
  ext y
  constructor
  · intro hy r
    change b' r ≤ ∑ l, A' r l * y l
    cases her : e r with
    | inl k =>
        have hk := k.2
        simpa [A', b', her] using hy.1 k.1 hk
    | inr ij =>
        have hi : 0 < A ij.1.1 (Fin.last n) := ij.1.2
        have hj : A ij.2.1 (Fin.last n) < 0 := ij.2.2
        have hbound := hy.2 ij.1.1 ij.2.1 hi hj
        simp only [LinearOptimization.fourierMotzkinBound] at hbound
        simp only [A', b', her]
        change
          b ij.1.1 / A ij.1.1 (Fin.last n) -
              b ij.2.1 / A ij.2.1 (Fin.last n) ≤
            ∑ l, (A ij.1.1 l.castSucc / A ij.1.1 (Fin.last n) -
              A ij.2.1 l.castSucc / A ij.2.1 (Fin.last n)) * y l
        have hsum_i :
            (∑ l, A ij.1.1 l.castSucc * y l) / A ij.1.1 (Fin.last n) =
              ∑ l, (A ij.1.1 l.castSucc / A ij.1.1 (Fin.last n)) * y l := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro l _
          ring
        have hsum_j :
            (∑ l, A ij.2.1 l.castSucc * y l) / A ij.2.1 (Fin.last n) =
              ∑ l, (A ij.2.1 l.castSucc / A ij.2.1 (Fin.last n)) * y l := by
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro l _
          ring
        rw [sub_div, hsum_i, sub_div, hsum_j] at hbound
        calc
          b ij.1.1 / A ij.1.1 (Fin.last n) -
                b ij.2.1 / A ij.2.1 (Fin.last n) ≤
              (∑ l, (A ij.1.1 l.castSucc / A ij.1.1 (Fin.last n)) * y l) -
                ∑ l, (A ij.2.1 l.castSucc / A ij.2.1 (Fin.last n)) * y l := by
            linarith
          _ = ∑ l, (A ij.1.1 l.castSucc / A ij.1.1 (Fin.last n) -
                A ij.2.1 l.castSucc / A ij.2.1 (Fin.last n)) * y l := by
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro l _
            ring
  · intro hy
    change b' ≤ A'.mulVec y at hy
    constructor
    · intro k hk
      let z : Z := ⟨k, hk⟩
      let r : Fin (Fintype.card I) := e.symm (Sum.inl z)
      have hr := hy r
      change b' r ≤ ∑ l, A' r l * y l at hr
      simpa [A', b', r, z] using hr
    · intro i j hi hj
      let p : P := ⟨i, hi⟩
      let q : N := ⟨j, hj⟩
      let r : Fin (Fintype.card I) := e.symm (Sum.inr (p, q))
      have hr := hy r
      change b' r ≤ ∑ l, A' r l * y l at hr
      simp only [A', b', r, p, q, e, Equiv.apply_symm_apply] at hr
      simp only [LinearOptimization.fourierMotzkinBound]
      have hsum_i :
          (∑ l, A i l.castSucc * y l) / A i (Fin.last n) =
            ∑ l, (A i l.castSucc / A i (Fin.last n)) * y l := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro l _
        ring
      have hsum_j :
          (∑ l, A j l.castSucc * y l) / A j (Fin.last n) =
            ∑ l, (A j l.castSucc / A j (Fin.last n)) * y l := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro l _
        ring
      rw [sub_div, hsum_i, sub_div, hsum_j]
      have hdiff :
          (∑ l, (A i l.castSucc / A i (Fin.last n)) * y l) -
              ∑ l, (A j l.castSucc / A j (Fin.last n)) * y l =
            ∑ l, (A i l.castSucc / A i (Fin.last n) -
              A j l.castSucc / A j (Fin.last n)) * y l := by
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro l _
        ring
      rw [← hdiff] at hr
      linarith
end R6RayHelper6

/- Accepted Prove2Me helper 5f00401c-20fe-404a-b0f3-718e95e40d10, submission e9104980-a86a-4040-87db-ad69eb9b6175, author Harry_Xu. -/
section R6RayHelper7
theorem LinearOptimization.polyhedron_projection {m n k : ℕ}
    (A : Matrix (Fin m) (Fin (n + k)) ℝ) (b : Fin m → ℝ) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin n) ℝ) (b' : Fin m' → ℝ),
      {x : Fin n → ℝ | ∃ y : Fin k → ℝ,
          Fin.append x y ∈ LinearOptimization.polyhedron A b} =
        LinearOptimization.polyhedron A' b' := by
  classical
  induction k generalizing m with
  | zero =>
      refine ⟨m, A, b, ?_⟩
      ext x
      constructor
      · rintro ⟨y, hy⟩
        have hy0 : y = Fin.elim0 := Subsingleton.elim _ _
        subst y
        simpa using hy
      · intro hx
        exact ⟨Fin.elim0, by simpa using hx⟩
  | succ k ih =>
      obtain ⟨m₁, A₁, b₁, hpoly⟩ :=
        LinearOptimization.fourier_motzkin_eliminate_is_polyhedron A b
      have hlast :
          (fun z : Fin (n + k + 1) → ℝ => fun l : Fin (n + k) => z l.castSucc) ''
              LinearOptimization.polyhedron A b =
            LinearOptimization.polyhedron A₁ b₁ := by
        calc
          _ = LinearOptimization.fourierMotzkinEliminate A b :=
            (LinearOptimization.fourier_motzkin_projection A b).symm
          _ = _ := hpoly
      obtain ⟨m₂, A₂, b₂, hrest⟩ := ih A₁ b₁
      refine ⟨m₂, A₂, b₂, ?_⟩
      rw [← hrest]
      ext x
      constructor
      · rintro ⟨ys, hys⟩
        refine ⟨Fin.init ys, ?_⟩
        rw [← hlast]
        refine ⟨Fin.snoc (Fin.append x (Fin.init ys)) (ys (Fin.last k)), ?_, ?_⟩
        · rw [← Fin.append_snoc, Fin.snoc_init_self]
          exact hys
        · funext l
          simp
      · rintro ⟨y, hy⟩
        have himage : Fin.append x y ∈
            (fun z : Fin (n + k + 1) → ℝ => fun l : Fin (n + k) => z l.castSucc) ''
              LinearOptimization.polyhedron A b := by
          rw [hlast]
          exact hy
        rcases himage with ⟨z, hz, hzproj⟩
        refine ⟨Fin.snoc y (z (Fin.last (n + k))), ?_⟩
        have hzinit : Fin.init z = Fin.append x y := by
          exact hzproj
        rw [Fin.append_snoc, ← hzinit]
        have hsnoc : Fin.snoc (Fin.init z) (z (Fin.last (n + k))) = z := by
          apply Fin.snoc_init_self
        rw [hsnoc]
        exact hz
end R6RayHelper7

/- Accepted Prove2Me helper 39d445f1-e8f7-4cfd-af28-af7d117e1a7f, submission 6b03ca9b-58f1-4bbf-924d-190f67881ae4, author Harry_Xu. -/
section R6RayHelper8
open Matrix

namespace LinearOptimization

def graphMatrix {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin p) (Fin n) ℝ) :
    Matrix (Fin (m + (p + (p + 1)))) (Fin (p + n)) ℝ :=
  fun i j =>
    Fin.addCases
      (fun r => Fin.addCases (fun _ => 0) (fun c => A r c) j)
      (fun i' => Fin.addCases
        (fun r => Fin.addCases (fun q => if q = r then -1 else 0) (fun c => M r c) j)
        (fun q => Fin.lastCases
          0
          (fun r => Fin.addCases (fun q => if q = r then 1 else 0) (fun c => -M r c) j)
          q)
        i')
      i

def graphRhs {m p : ℕ} (b : Fin m → ℝ) : Fin (m + (p + (p + 1))) → ℝ :=
  Fin.addCases b (fun _ => 0)

theorem graph_mulVec_orig {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin p) (Fin n) ℝ)
    (y : Fin p → ℝ) (x : Fin n → ℝ) (r : Fin m) :
    (graphMatrix A M).mulVec (Fin.append y x)
        (Fin.castAdd (p + (p + 1)) r) = A.mulVec x r := by
  simp [graphMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_add]

theorem graph_mulVec_lower {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin p) (Fin n) ℝ)
    (y : Fin p → ℝ) (x : Fin n → ℝ) (r : Fin p) :
    (graphMatrix A M).mulVec (Fin.append y x)
        (Fin.natAdd m (Fin.castAdd (p + 1) r)) = M.mulVec x r - y r := by
  simp [graphMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
  ring

theorem graph_mulVec_upper {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin p) (Fin n) ℝ)
    (y : Fin p → ℝ) (x : Fin n → ℝ) (r : Fin p) :
    (graphMatrix A M).mulVec (Fin.append y x)
        (Fin.natAdd m (Fin.natAdd p r.castSucc)) = y r - M.mulVec x r := by
  simp [graphMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
  ring

theorem graph_mulVec_dummy {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (M : Matrix (Fin p) (Fin n) ℝ)
    (y : Fin p → ℝ) (x : Fin n → ℝ) :
    (graphMatrix A M).mulVec (Fin.append y x)
        (Fin.natAdd m (Fin.natAdd p (Fin.last p))) = 0 := by
  have hrow : graphMatrix A M (Fin.natAdd m (Fin.natAdd p (Fin.last p))) =
      (fun _ => 0) := by
    funext j
    unfold graphMatrix
    rw [Fin.addCases_right, Fin.addCases_right, Fin.lastCases_last]
  change dotProduct (graphMatrix A M (Fin.natAdd m (Fin.natAdd p (Fin.last p))))
      (Fin.append y x) = 0
  rw [hrow]
  simp [dotProduct]

theorem graph_mem_iff {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (M : Matrix (Fin p) (Fin n) ℝ) (y : Fin p → ℝ) (x : Fin n → ℝ) :
    Fin.append y x ∈ polyhedron (graphMatrix A M) (graphRhs b) ↔
      x ∈ polyhedron A b ∧ y = M.mulVec x := by
  constructor
  · intro h
    constructor
    · intro r
      simpa [graphRhs, graph_mulVec_orig] using
        h (Fin.castAdd (p + (p + 1)) r)
    · funext r
      have hlo := h (Fin.natAdd m (Fin.castAdd (p + 1) r))
      simp [graphRhs, graph_mulVec_lower] at hlo
      have hhi := h (Fin.natAdd m (Fin.natAdd p r.castSucc))
      simp [graphRhs, graph_mulVec_upper] at hhi
      linarith
  · rintro ⟨hx, rfl⟩ i
    refine Fin.addCases
      (motive := fun i => graphRhs b i ≤
        (graphMatrix A M).mulVec (Fin.append (M.mulVec x) x) i)
      (fun r => by simpa [graphRhs, graph_mulVec_orig] using hx r)
      (fun i' => by
        refine Fin.addCases
          (motive := fun i' => graphRhs b (Fin.natAdd m i') ≤
            (graphMatrix A M).mulVec (Fin.append (M.mulVec x) x) (Fin.natAdd m i'))
          (fun r => by simp [graphRhs, graph_mulVec_lower])
          (fun q => by
            refine Fin.lastCases
              (motive := fun q => graphRhs b (Fin.natAdd m (Fin.natAdd p q)) ≤
                (graphMatrix A M).mulVec (Fin.append (M.mulVec x) x)
                  (Fin.natAdd m (Fin.natAdd p q)))
              (by
                change graphRhs b (Fin.last (m + (p + p))) ≤
                  (graphMatrix A M).mulVec (Fin.append (M.mulVec x) x)
                    (Fin.last (m + (p + p)))
                have hidx : Fin.last (m + (p + p)) =
                    Fin.natAdd m (Fin.natAdd p (Fin.last p)) := by
                  ext
                  simp
                rw [hidx]
                have hbzero : graphRhs b (Fin.natAdd m (Fin.natAdd p (Fin.last p))) = 0 := by
                  simp only [graphRhs, Fin.addCases_right]
                rw [hbzero, graph_mulVec_dummy]
                )
              (fun r => by simp [graphRhs, graph_mulVec_upper]) q)
          i')
      i

end LinearOptimization

theorem LinearOptimization.polyhedron_linear_image {m n p : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (M : Matrix (Fin p) (Fin n) ℝ) :
    ∃ (m' : ℕ) (A' : Matrix (Fin m') (Fin p) ℝ) (b' : Fin m' → ℝ),
      M.mulVec '' LinearOptimization.polyhedron A b =
        LinearOptimization.polyhedron A' b' := by
  obtain ⟨m', A', b', hproj⟩ :=
    LinearOptimization.polyhedron_projection
      (LinearOptimization.graphMatrix A M) (LinearOptimization.graphRhs b)
  refine ⟨m', A', b', ?_⟩
  rw [← hproj]
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (LinearOptimization.graph_mem_iff A b M (M.mulVec x) x).2 ⟨hx, rfl⟩⟩
  · rintro ⟨x, hx⟩
    obtain ⟨hxp, hy⟩ := (LinearOptimization.graph_mem_iff A b M y x).1 hx
    exact ⟨x, hxp, hy.symm⟩
end R6RayHelper8

/- Accepted Prove2Me helper 00c98cf7-7b73-44ef-9acd-b43230ea4032, submission c07ab102-60b7-46c1-871b-0aa6e293380f, author Harry_Xu. -/
section R6RayHelper9
open Matrix

theorem LinearOptimization.polyhedron_closed {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    IsClosed (LinearOptimization.polyhedron A b) := by
  rw [show LinearOptimization.polyhedron A b =
      ⋂ i : Fin m, {x : Fin n → ℝ | b i ≤ A.mulVec x i} by
    ext x
    simp only [LinearOptimization.polyhedron, Set.mem_setOf_eq,
      Set.mem_iInter, Pi.le_def]]
  apply isClosed_iInter
  intro i
  apply isClosed_le continuous_const
  exact (continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)
end R6RayHelper9

/- Accepted Prove2Me helper 0fb3b53a-786e-4c09-bd35-aed99bf2561a, submission 022fe99a-15e3-4b19-bc9e-512f13b0e5c3, author Harry_Xu. -/
section R6RayHelper10
open Matrix

theorem LinearOptimization.separating_hyperplane_polyhedron {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : S.Nonempty) (hclosed : IsClosed S) (hconv : Convex ℝ S)
    (xstar : Fin n → ℝ) (hx : xstar ∉ S) :
    ∃ c : Fin n → ℝ, ∀ x ∈ S, c ⬝ᵥ xstar < c ⬝ᵥ x := by
  classical
  obtain ⟨f, u, hstar, hf⟩ :=
    geometric_hahn_banach_point_closed hconv hclosed hx
  let c : Fin n → ℝ := fun i ↦ f (Pi.single i 1)
  have hdot (z : Fin n → ℝ) : c ⬝ᵥ z = f z := by
    calc
      c ⬝ᵥ z = ∑ i : Fin n, f (z i • Pi.single i 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [c, mul_comm]
      _ = f (∑ i : Fin n, z i • Pi.single i 1) := by
        rw [map_sum]
      _ = f z := by
        congr 1
        funext i
        simp [Pi.single_apply]
  refine ⟨c, fun x hxS ↦ ?_⟩
  have hsep : f xstar < f x := hstar.trans (hf x hxS)
  simpa [hdot] using hsep
end R6RayHelper10

/- Accepted Prove2Me helper 3f00768b-7c17-4b07-a2ff-4aba77328692, submission 6ba20039-3526-4f57-9a4a-2b50b7336066, author Harry_Xu. -/
section R6RayHelper11
open Matrix

theorem LinearOptimization.farkas_lemma {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) :
    Xor' (∃ x : Fin n → ℝ, 0 ≤ x ∧ A.mulVec x = b)
      (∃ p : Fin m → ℝ, 0 ≤ Aᵀ.mulVec p ∧ p ⬝ᵥ b < 0) := by
  classical
  let C : Set (Fin m → ℝ) := A.mulVec '' {x : Fin n → ℝ | 0 ≤ x}
  have horthant :
      LinearOptimization.polyhedron (1 : Matrix (Fin n) (Fin n) ℝ) 0 =
        {x : Fin n → ℝ | 0 ≤ x} := by
    ext x
    simp [LinearOptimization.polyhedron, Pi.le_def]
  obtain ⟨r, D, e, himage⟩ :=
    LinearOptimization.polyhedron_linear_image
      (1 : Matrix (Fin n) (Fin n) ℝ) 0 A
  have hCpoly : C = LinearOptimization.polyhedron D e := by
    simpa [C, horthant] using himage
  have hCclosed : IsClosed C := by
    rw [hCpoly]
    exact LinearOptimization.polyhedron_closed D e
  let T : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) :=
    { toFun := A.mulVec
      map_add' := A.mulVec_add
      map_smul' := A.mulVec_smul }
  have hCconv : Convex ℝ C := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ a c ha hc hac
    refine ⟨a • x + c • y, ?_, ?_⟩
    · intro j
      exact add_nonneg (mul_nonneg ha (hx j)) (mul_nonneg hc (hy j))
    · simp [T, Matrix.mulVec_add, Matrix.mulVec_smul]
  have hCzero : (0 : Fin m → ℝ) ∈ C := by
    refine ⟨0, ?_, ?_⟩
    · simp
    · simp
  have hdual (p : Fin m → ℝ) (x : Fin n → ℝ) :
      p ⬝ᵥ A.mulVec x = Aᵀ.mulVec p ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec]
    congr 1
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  by_cases hbC : b ∈ C
  · left
    constructor
    · rcases hbC with ⟨x, hx, hAx⟩
      exact ⟨x, hx, hAx⟩
    · rintro ⟨p, hp, hpb⟩
      rcases hbC with ⟨x, hx, hAx⟩
      have hnonneg : 0 ≤ Aᵀ.mulVec p ⬝ᵥ x := by
        exact Finset.sum_nonneg fun j hj ↦ mul_nonneg (hp j) (hx j)
      rw [← hdual, hAx] at hnonneg
      linarith
  · right
    constructor
    · obtain ⟨p, hsep⟩ :=
        LinearOptimization.separating_hyperplane_polyhedron
          C ⟨0, hCzero⟩ hCclosed hCconv b hbC
      have hpb : p ⬝ᵥ b < 0 := by
        simpa using hsep 0 hCzero
      refine ⟨p, ?_, hpb⟩
      intro j
      by_contra hj
      have hq : Aᵀ.mulVec p j < 0 := lt_of_not_ge hj
      let q : ℝ := Aᵀ.mulVec p j
      let z : Fin n → ℝ :=
        (p ⬝ᵥ b / q + 1) • Pi.single j 1
      have hscale : 0 < p ⬝ᵥ b / q + 1 := by
        have : 0 < p ⬝ᵥ b / q := div_pos_of_neg_of_neg hpb (by simpa [q] using hq)
        linarith
      have hz : 0 ≤ z := by
        intro l
        simp only [z, Pi.smul_apply, smul_eq_mul]
        apply mul_nonneg hscale.le
        by_cases hlj : l = j <;> simp [Pi.single_apply, hlj]
      have hAz : A.mulVec z ∈ C := ⟨z, hz, rfl⟩
      have hs := hsep (A.mulVec z) hAz
      have heval : Aᵀ.mulVec p ⬝ᵥ z =
          (p ⬝ᵥ b / q + 1) * q := by
        simp [z, q, dotProduct, Pi.single_apply, mul_comm]
      rw [hdual, heval] at hs
      have hlt : (p ⬝ᵥ b / q + 1) * q < p ⬝ᵥ b := by
        have hqne : q ≠ 0 := ne_of_lt (by simpa [q] using hq)
        field_simp [hqne]
        linarith [hq]
      linarith
    · rintro ⟨x, hx, hAx⟩
      exact hbC ⟨x, hx, hAx⟩
end R6RayHelper11

/- Accepted Prove2Me helper a03c5421-dd3c-40f7-8dd6-38fd6fa91ecf, submission 19f5b071-ddbb-442b-b3fc-7413851c6148, author Harry_Xu. -/
section R6RayHelper12
open Matrix

theorem LinearOptimization.farkas_cone_corollary {m n : ℕ} (A : Fin n → (Fin m → ℝ))
    (b : Fin m → ℝ)
    (h : ∀ p : Fin m → ℝ, (∀ i, 0 ≤ p ⬝ᵥ A i) → 0 ≤ p ⬝ᵥ b) :
    ∃ lam : Fin n → ℝ, (∀ i, 0 ≤ lam i) ∧ b = ∑ i, lam i • A i := by
  classical
  let M : Matrix (Fin m) (Fin n) ℝ := fun i j ↦ A j i
  rcases LinearOptimization.farkas_lemma M b with hfirst | hsecond
  · rcases hfirst.1 with ⟨lam, hlam, hM⟩
    refine ⟨lam, hlam, ?_⟩
    rw [← hM]
    funext i
    simp [M, Matrix.mulVec, dotProduct, mul_comm]
  · rcases hsecond.1 with ⟨p, hp, hpb⟩
    have hpA : ∀ j, 0 ≤ p ⬝ᵥ A j := by
      intro j
      simpa [M, Matrix.mulVec, Matrix.transpose, Matrix.of_apply, dotProduct, mul_comm] using hp j
    exact ((not_lt_of_ge (h p hpA)) hpb).elim
end R6RayHelper12

open Matrix LinearOptimization

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hext : (Set.extremePoints ℝ (polyhedron A b)).Nonempty) :
    lpValue c (polyhedron A b) = ⊥ ↔
      ∃ d : Fin n → ℝ, IsExtremeRay A d ∧ c ⬝ᵥ d < 0 := by
  classical
  obtain ⟨x0, hx0⟩ := hext
  have hne : (polyhedron A b).Nonempty := ⟨x0, hx0.1⟩
  have hrows : ∃ s : Finset (Fin m), s.card = n ∧
      LinearIndependent ℝ (fun i : s => A i.1) := by
    apply ((polyhedron_extreme_point_existence A b hne).out 0 2).mp
    exact ⟨x0, hx0⟩
  have hcone := cone_pointed_iff_extreme_zero A
  have hpointed : IsPointedCone (polyhedron A 0) := hcone.1.mpr (hcone.2.mpr hrows)
  constructor
  · intro hbot
    apply (cone_unbounded_iff_extreme_ray A c hpointed).mp
    by_contra hnotbot
    have hnonneg : ∀ d ∈ polyhedron A 0, 0 ≤ c ⬝ᵥ d := by
      intro d hd
      by_contra hn
      have hneg : c ⬝ᵥ d < 0 := lt_of_not_ge hn
      have hunb := LOCore.unbounded_of_ray A 0 c
        (x := 0) (e := d) (by intro i; simp) hd hneg
      apply hnotbot
      rw [lpValue, iInf_eq_bot]
      intro z hz
      induction z using EReal.rec with
      | bot => exact (lt_irrefl _ hz).elim
      | coe r =>
        obtain ⟨w, hw, hc⟩ := hunb r
        exact ⟨w, by simpa [hw] using EReal.coe_lt_coe_iff.mpr hc⟩
      | top =>
        have hzero : (0 : Fin n → ℝ) ∈ polyhedron A 0 := by intro i; simp
        exact ⟨0, by simpa [hzero] using EReal.coe_lt_top (0 : ℝ)⟩
    obtain ⟨lam, hlam, hcost⟩ := farkas_cone_corollary A c (by
      intro d hd
      rw [dotProduct_comm d c]
      apply hnonneg d
      intro i
      change 0 ≤ A i ⬝ᵥ d
      rw [dotProduct_comm (A i) d]
      exact hd i)
    have hlower : ∀ y ∈ polyhedron A b,
        (∑ i, lam i * b i) ≤ c ⬝ᵥ y := by
      intro y hy
      rw [hcost, sum_dotProduct]
      apply Finset.sum_le_sum
      intro i _
      rw [smul_dotProduct, smul_eq_mul]
      exact mul_le_mul_of_nonneg_left (hy i) (hlam i)
    have hfinite : (((∑ i, lam i * b i) : ℝ) : EReal) ≤ lpValue c (polyhedron A b) := by
      rw [lpValue]
      apply le_iInf
      intro y
      apply le_iInf
      intro hy
      exact EReal.coe_le_coe_iff.mpr (hlower y hy)
    rw [hbot] at hfinite
    exact (not_le_of_gt (EReal.bot_lt_coe _)) hfinite
  · rintro ⟨d, hd, hcd⟩
    have hunb := LOCore.unbounded_of_ray A b c hx0.1 hd.1 hcd
    rw [lpValue, iInf_eq_bot]
    intro z hz
    induction z using EReal.rec with
    | bot => exact (lt_irrefl _ hz).elim
    | coe r =>
      obtain ⟨w, hw, hc⟩ := hunb r
      exact ⟨w, by simpa [hw] using EReal.coe_lt_coe_iff.mpr hc⟩
    | top => exact ⟨x0, by simpa [hx0.1] using EReal.coe_lt_top (c ⬝ᵥ x0)⟩
