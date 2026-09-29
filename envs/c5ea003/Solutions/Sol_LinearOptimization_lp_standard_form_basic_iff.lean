-- Prove2me | solution 1 for LinearOptimization.lp_standard_form_basic_iff
-- status  : ACCEPTED   (prove)
-- author  : @MKPynnic
-- created : 2026-08-05T05:59:11.73707+00:00
-- url     : https://prove2.me/submissions/fde7dacc-82d1-452a-b908-35c16be8b9f6

import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Algebra.BigOperators.Pi
import Definitions.Def_BasicSolution

open Matrix LinearOptimization

/-- The subspace of vectors orthogonal to a fixed `d`. -/
private def orthTo {n : ℕ} (d : Fin n → ℝ) : Submodule ℝ (Fin n → ℝ) where
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

/-- Every linear functional on `Fin n → ℝ` is `v ↦ v ⬝ᵥ d` for some `d`. -/
private lemma dual_eq_dotProduct {n : ℕ} (f : Module.Dual ℝ (Fin n → ℝ)) :
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

/-- If only `0` is orthogonal to every element of `S`, then `S` spans. -/
private lemma span_eq_top_of_orth {n : ℕ} (S : Set (Fin n → ℝ))
    (h : ∀ v : Fin n → ℝ, (∀ w ∈ S, w ⬝ᵥ v = 0) → v = 0) : Submodule.span ℝ S = ⊤ := by
  by_contra hne
  obtain ⟨f, hf0, hfmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance
  obtain ⟨d, hd⟩ := dual_eq_dotProduct f
  have hzero : ∀ w ∈ S, w ⬝ᵥ d = 0 := by
    intro w hw
    have h1 : f w ∈ Submodule.map f (Submodule.span ℝ S) :=
      Submodule.mem_map_of_mem (Submodule.subset_span hw)
    rw [hfmap, Submodule.mem_bot] at h1
    rw [← hd]; exact h1
  exact hf0 (LinearMap.ext fun v => by simp [hd v, h d hzero])

/-- Conversely, if `S` spans then only `0` is orthogonal to all of `S`. -/
private lemma orth_of_span_top {n : ℕ} (S : Set (Fin n → ℝ))
    (hS : Submodule.span ℝ S = ⊤) {v : Fin n → ℝ} (h : ∀ w ∈ S, w ⬝ᵥ v = 0) : v = 0 := by
  have hle : (⊤ : Submodule ℝ (Fin n → ℝ)) ≤ orthTo v := by
    rw [← hS]; exact Submodule.span_le.mpr h
  exact dotProduct_self_eq_zero.mp (hle (Submodule.mem_top))

/-- `n` vectors in `ℝⁿ` are linearly independent exactly when no nonzero vector is
orthogonal to all of them. -/
private lemma indep_iff_orth {ι : Type} [Fintype ι] {n : ℕ} (f : ι → (Fin n → ℝ))
    (hcard : Fintype.card ι = n) :
    LinearIndependent ℝ f ↔ ∀ v : Fin n → ℝ, (∀ i, f i ⬝ᵥ v = 0) → v = 0 := by
  have hfr : Module.finrank ℝ (Fin n → ℝ) = n := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  constructor
  · intro hli v hv
    have hspan : Submodule.span ℝ (Set.range f) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by rw [hcard, hfr])
    refine orth_of_span_top _ hspan ?_
    rintro w ⟨i, rfl⟩
    exact hv i
  · intro h
    refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ (by rw [hcard, hfr])
    rw [span_eq_top_of_orth (Set.range f) ?_]
    · intro v hv
      exact h v (fun i => hv (f i) ⟨i, rfl⟩)

/-- `A x` is the combination of the columns of `A` with coefficients `x`. -/
private lemma mulVec_eq_sum_cols {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℝ) :
    A.mulVec v = ∑ j, v j • Aᵀ j := by
  funext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

private lemma single_dot {n : ℕ} (j : Fin n) (y : Fin n → ℝ) :
    (Pi.single j (1:ℝ)) ⬝ᵥ y = y j := by
  simp [dotProduct, Pi.single_apply, Finset.sum_ite_eq']

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (hA : LinearIndependent ℝ (fun i => A i))
    (x : Fin n → ℝ) :
    IsBasicSolution (stdFormSystem A b) x ↔
      A.mulVec x = b ∧ ∃ B : Fin m ↪ Fin n, IsStdBasis A B ∧
        ∀ j, j ∉ Set.range B → x j = 0 := by
  classical
  have hfrn : Module.finrank ℝ (Fin n → ℝ) = n := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  have hfrm : Module.finrank ℝ (Fin m → ℝ) = m := by
    rw [Module.finrank_pi ℝ, Fintype.card_fin]
  have hInr : ∀ (j : Fin n) (y : Fin n → ℝ),
      (stdFormSystem A b (Sum.inr j)).IsActiveAt y ↔ y j = 0 := by
    intro j y
    show (Pi.single j (1:ℝ)) ⬝ᵥ y = 0 ↔ y j = 0
    rw [single_dot]
  -- The columns of `A` span `ℝᵐ`, because its rows are linearly independent.
  have hcolspan : Submodule.span ℝ (Set.range (fun j => Aᵀ j)) = (⊤ : Submodule ℝ (Fin m → ℝ)) := by
    refine span_eq_top_of_orth _ ?_
    intro u hu
    refine funext fun i => ?_
    have hcomb : ∑ i, u i • A i = 0 := by
      funext j
      have h1 := hu (Aᵀ j) ⟨j, rfl⟩
      simpa [dotProduct, Finset.sum_apply, Matrix.transpose_apply, mul_comm] using h1
    exact Fintype.linearIndependent_iff.mp hA u hcomb i
  constructor
  · -- basic solution ⟹ standard-form basis description
    rintro ⟨heq, s, hcard, hact, hli⟩
    have hAx : A.mulVec x = b := funext fun k => heq (Sum.inl k) rfl
    refine ⟨hAx, ?_⟩
    have hspanS : Submodule.span ℝ (Set.range (fun i : s => (stdFormSystem A b i.1).a)) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_coe, hcard, hfrn])
    have horth : ∀ v : Fin n → ℝ, (∀ i ∈ s, (stdFormSystem A b i).a ⬝ᵥ v = 0) → v = 0 := by
      intro v hv
      refine orth_of_span_top _ hspanS ?_
      rintro w ⟨i, rfl⟩
      exact hv i.1 i.2
    -- indices whose nonnegativity constraint sits in `s`, and their complement
    set Nf : Finset (Fin n) := Finset.univ.filter (fun j => Sum.inr j ∈ s) with hNf
    set Kf : Finset (Fin n) := Nfᶜ with hKf
    have hxN : ∀ j ∈ Nf, x j = 0 := by
      intro j hj
      simp only [hNf, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact (hInr j x).mp (hact _ hj)
    -- the columns indexed outside `Nf` are linearly independent
    have hKindep : LinearIndepOn ℝ (fun j => Aᵀ j) (↑Kf : Set (Fin n)) := by
      rw [LinearIndepOn, Fintype.linearIndependent_iff]
      intro g hg i0
      set v : Fin n → ℝ := fun j => if h : j ∈ Kf then g ⟨j, h⟩ else 0 with hvdef
      have hsum : ∑ j, v j • Aᵀ j = 0 := by
        have hrestrict : ∑ j, v j • Aᵀ j = ∑ j ∈ Kf, v j • Aᵀ j := by
          refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
          intro j _ hj
          simp [hvdef, hj]
        rw [hrestrict, ← Finset.sum_coe_sort Kf (fun j => v j • Aᵀ j)]
        refine Eq.trans (Finset.sum_congr rfl ?_) hg
        intro i _
        simp [hvdef, i.2]
      have hvA : A.mulVec v = 0 := by rw [mulVec_eq_sum_cols, hsum]
      have hv0 : v = 0 := by
        refine horth v ?_
        intro i hi
        cases i with
        | inl k =>
          have : A.mulVec v k = 0 := by rw [hvA]; rfl
          exact this
        | inr j =>
          have hjN : j ∈ Nf := by
            simp only [hNf, Finset.mem_filter, Finset.mem_univ, true_and]
            exact hi
          have hjK : j ∉ Kf := by simp [hKf, hjN]
          show (Pi.single j (1:ℝ)) ⬝ᵥ v = 0
          rw [single_dot]
          simp [hvdef, hjK]
      have := congrFun hv0 i0.1
      simpa [hvdef, i0.2] using this
    -- extend to a full basis of `ℝᵐ` using columns of `A`
    set E : Set (Fin n) := hKindep.extend (Set.subset_univ _) with hE
    have hKE : (↑Kf : Set (Fin n)) ⊆ E := hKindep.subset_extend _
    have hEindep : LinearIndepOn ℝ (fun j => Aᵀ j) E := hKindep.linearIndepOn_extend _
    have hEspan : Submodule.span ℝ ((fun j => Aᵀ j) '' E) = ⊤ := by
      rw [hKindep.span_image_extend_eq_span_image (Set.subset_univ _), Set.image_univ, hcolspan]
    haveI : Fintype ↥E := Fintype.ofFinite _
    have hEli : LinearIndependent ℝ (fun i : E => Aᵀ i.1) := hEindep
    have hEsp2 : Submodule.span ℝ (Set.range (fun i : E => Aᵀ i.1)) = ⊤ := by
      rw [← hEspan]
      congr 1
      exact (Set.image_eq_range _ _).symm
    let bas : Module.Basis ↥E ℝ (Fin m → ℝ) := Module.Basis.mk hEli (le_of_eq hEsp2.symm)
    have hcardE : Fintype.card ↥E = m := by
      have h := Module.finrank_eq_card_basis bas
      rw [hfrm] at h
      exact h.symm
    let e : Fin m ≃ ↥E := (Fintype.equivFinOfCardEq hcardE).symm
    have hBinj : Function.Injective (fun k : Fin m => (e k).1) := by
      intro k₁ k₂ h
      exact e.injective (Subtype.ext h)
    refine ⟨⟨fun k => (e k).1, hBinj⟩, ?_, ?_⟩
    · show LinearIndependent ℝ (fun k : Fin m => Aᵀ (e k).1)
      exact (linearIndependent_equiv e).mpr hEli
    · intro j hj
      have hjE : j ∉ E := by
        intro hmem
        exact hj ⟨e.symm ⟨j, hmem⟩, by simp⟩
      have hjK : j ∉ Kf := fun hc => hjE (hKE hc)
      have : j ∈ Nf := by
        by_contra hc
        exact hjK (by simp [hKf, hc])
      exact hxN j this
  · -- standard-form basis description ⟹ basic solution
    rintro ⟨hAx, B, hB, hxz⟩
    have hmn : m ≤ n := by
      have := Fintype.card_le_of_injective B B.injective
      simpa using this
    refine ⟨?_, ?_⟩
    · intro i hi
      cases i with
      | inl k => exact congrFun hAx k
      | inr j => exact absurd hi (by simp [stdFormSystem])
    · set T : Finset (Fin n) := (Finset.univ.image B)ᶜ with hT
      have hmemT : ∀ j : Fin n, j ∈ T ↔ j ∉ Set.range B := by
        intro j
        simp [hT, Set.mem_range]
      refine ⟨(Finset.univ.image Sum.inl) ∪ (T.image Sum.inr), ?_, ?_, ?_⟩
      · have hdisj : Disjoint (Finset.univ.image (Sum.inl : Fin m → Fin m ⊕ Fin n))
            (T.image (Sum.inr : Fin n → Fin m ⊕ Fin n)) := by
          rw [Finset.disjoint_left]
          rintro a ha hb
          simp only [Finset.mem_image] at ha hb
          obtain ⟨k, _, rfl⟩ := ha
          obtain ⟨j, _, hj⟩ := hb
          simp at hj
        rw [Finset.card_union_of_disjoint hdisj,
          Finset.card_image_of_injective _ (Sum.inl_injective),
          Finset.card_image_of_injective _ (Sum.inr_injective), Finset.card_univ,
          Fintype.card_fin, hT, Finset.card_compl,
          Finset.card_image_of_injective _ B.injective, Finset.card_univ, Fintype.card_fin,
          Fintype.card_fin]
        omega
      · intro i hi
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hi
        rcases hi with ⟨k, rfl⟩ | ⟨j, hj, rfl⟩
        · exact congrFun hAx k
        · exact (hInr j x).mpr (hxz j ((hmemT j).mp hj))
      · -- linear independence of the chosen constraint vectors
        have hcardT : Fintype.card ↥((Finset.univ.image (Sum.inl : Fin m → Fin m ⊕ Fin n)) ∪
            (T.image Sum.inr)) = n := by
          rw [Fintype.card_coe]
          have hdisj : Disjoint (Finset.univ.image (Sum.inl : Fin m → Fin m ⊕ Fin n))
              (T.image (Sum.inr : Fin n → Fin m ⊕ Fin n)) := by
            rw [Finset.disjoint_left]
            rintro a ha hb
            simp only [Finset.mem_image] at ha hb
            obtain ⟨k, _, rfl⟩ := ha
            obtain ⟨j, _, hj⟩ := hb
            simp at hj
          rw [Finset.card_union_of_disjoint hdisj,
            Finset.card_image_of_injective _ (Sum.inl_injective),
            Finset.card_image_of_injective _ (Sum.inr_injective), Finset.card_univ,
            Fintype.card_fin, hT, Finset.card_compl,
            Finset.card_image_of_injective _ B.injective, Finset.card_univ, Fintype.card_fin,
            Fintype.card_fin]
          omega
        rw [indep_iff_orth _ hcardT]
        intro v hv
        -- `v` is killed by every row of `A`, and vanishes off `range B`
        have hrow : ∀ k : Fin m, A k ⬝ᵥ v = 0 := by
          intro k
          have hmem : (Sum.inl k : Fin m ⊕ Fin n) ∈
              (Finset.univ.image (Sum.inl : Fin m → Fin m ⊕ Fin n)) ∪ (T.image Sum.inr) := by
            simp
          exact hv ⟨_, hmem⟩
        have hoff : ∀ j : Fin n, j ∉ Set.range B → v j = 0 := by
          intro j hj
          have hmem : (Sum.inr j : Fin m ⊕ Fin n) ∈
              (Finset.univ.image (Sum.inl : Fin m → Fin m ⊕ Fin n)) ∪ (T.image Sum.inr) := by
            simp only [Finset.mem_union, Finset.mem_image]
            exact Or.inr ⟨j, (hmemT j).mpr hj, rfl⟩
          have := hv ⟨_, hmem⟩
          rw [show (stdFormSystem A b (Sum.inr j)).a = Pi.single j (1:ℝ) from rfl,
            single_dot] at this
          exact this
        have hvA : A.mulVec v = 0 := funext fun k => hrow k
        have hcolsum : ∑ k : Fin m, v (B k) • Aᵀ (B k) = 0 := by
          have h1 : ∑ j, v j • Aᵀ j = 0 := by rw [← mulVec_eq_sum_cols, hvA]
          have h2 : ∑ j, v j • Aᵀ j = ∑ j ∈ Finset.univ.image B, v j • Aᵀ j := by
            refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
            intro j _ hj
            have : j ∉ Set.range B := by
              intro hc; obtain ⟨k, rfl⟩ := hc; exact hj (by simp)
            rw [hoff j this, zero_smul]
          rw [h2, Finset.sum_image (fun a _ b _ h => B.injective h)] at h1
          exact h1
        have hzB : ∀ k, v (B k) = 0 :=
          Fintype.linearIndependent_iff.mp hB (fun k => v (B k)) hcolsum
        funext j
        by_cases hj : j ∈ Set.range B
        · obtain ⟨k, rfl⟩ := hj
          exact hzB k
        · exact hoff j hj
