-- Prove2me | solution 1 for LinearOptimization.simplex_reduced_cost_optimality
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T03:09:32.156494+00:00
-- url     : https://prove2.me/submissions/7decba78-c5ec-423f-893a-b2eef694501f

import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Definitions.Def_Polyhedron
import Definitions.Def_LinearOptimization_ReducedCost
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Mathlib.Tactic.Linarith

open Matrix

private lemma eq_zero_of_kernel_of_eq_zero_off_basis {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (B : Fin m ↪ Fin n)
    (hB : LinearOptimization.IsStdBasis A B) (d : Fin n → ℝ)
    (hAd : A.mulVec d = 0) (hd : ∀ j ∉ Set.range B, d j = 0) : d = 0 := by
  classical
  have hcols : LinearIndependent ℝ (LinearOptimization.basisMatrix A B).col := by
    simpa [Matrix.col, LinearOptimization.basisMatrix] using hB
  have hunit : IsUnit (LinearOptimization.basisMatrix A B) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  let alpha : Fin m → ℝ := fun i => d (B i)
  have hBM : (LinearOptimization.basisMatrix A B).mulVec alpha = 0 := by
    funext i
    change (∑ k : Fin m, A i (B k) * d (B k)) = 0
    have himage : (∑ k : Fin m, A i (B k) * d (B k)) =
        ∑ j ∈ Finset.univ.image B, A i j * d j := by
      rw [Finset.sum_image]
      exact fun _ _ _ _ h => B.injective h
    rw [himage]
    have hall : (∑ j ∈ Finset.univ.image B, A i j * d j) =
        ∑ j : Fin n, A i j * d j := by
      apply Finset.sum_subset (by intro j hj; simp)
      intro j _ hj
      have hjrange : j ∉ Set.range B := by
        intro hr
        obtain ⟨k, rfl⟩ := hr
        exact hj (by simp)
      rw [hd j hjrange, mul_zero]
    rw [hall]
    simpa [Matrix.mulVec, dotProduct] using congrFun hAd i
  have halpha : alpha = 0 :=
    (Matrix.mulVec_injective_iff_isUnit.mpr hunit) (by simpa using hBM)
  funext j
  by_cases hj : j ∈ Set.range B
  · obtain ⟨i, rfl⟩ := hj
    exact congrFun halpha i
  · exact hd j hj

private lemma reducedCost_dot_kernel {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (c : Fin n → ℝ)
    (B : Fin m ↪ Fin n) (hB : LinearOptimization.IsStdBasis A B)
    (d : Fin n → ℝ) (hAd : A.mulVec d = 0) :
    LinearOptimization.reducedCost A c B ⬝ᵥ d = c ⬝ᵥ d := by
  classical
  have hcols : LinearIndependent ℝ (LinearOptimization.basisMatrix A B).col := by
    simpa [Matrix.col, LinearOptimization.basisMatrix] using hB
  letI : Invertible (LinearOptimization.basisMatrix A B) :=
    (Matrix.linearIndependent_cols_iff_isUnit.mp hcols).invertible
  let z : Fin m → ℝ := ∑ j : Fin n,
    d j • (LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun i => A i j)
  have hz : z = 0 := by
    funext k
    dsimp [z]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    change (∑ j : Fin n, d j *
      ((LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun i => A i j)) k) = 0
    simp only [Matrix.mulVec, dotProduct]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hrearrange :
        (∑ i : Fin m, ∑ j : Fin n,
          d j * ((LinearOptimization.basisMatrix A B)⁻¹ k i * A i j)) =
        ∑ i : Fin m, (LinearOptimization.basisMatrix A B)⁻¹ k i *
          (∑ j : Fin n, A i j * d j) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hrearrange]
    have hrow : ∀ i : Fin m, (∑ j : Fin n, A i j * d j) = 0 := by
      intro i
      simpa [Matrix.mulVec, dotProduct] using congrFun hAd i
    apply Finset.sum_eq_zero
    intro i _
    rw [hrow i, mul_zero]
  have hcross : (∑ j : Fin n,
      ((fun i => c (B i)) ⬝ᵥ
        (LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun i => A i j)) * d j) = 0 := by
    calc
      _ = (fun i => c (B i)) ⬝ᵥ z := by
        simp only [dotProduct, z, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hz, dotProduct_zero]
  unfold LinearOptimization.reducedCost
  simp only [dotProduct, sub_mul]
  rw [Finset.sum_sub_distrib]
  change (∑ j : Fin n, c j * d j) -
    (∑ j : Fin n, ((fun i => c (B i)) ⬝ᵥ
      (LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun i => A i j)) * d j) =
      ∑ j : Fin n, c j * d j
  rw [hcross, sub_zero]

private lemma feasible_step_of_tangent_std {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (x d : Fin n → ℝ) (hx : x ∈ LinearOptimization.stdPolyhedron A b)
    (hAd : A.mulVec d = 0) (hsign : ∀ j, x j = 0 → 0 ≤ d j) :
    ∃ t > (0 : ℝ), x + t • d ∈ LinearOptimization.stdPolyhedron A b := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter (fun j => d j < 0)
  by_cases hs : s.Nonempty
  · obtain ⟨j₀, hj₀s, hj₀min⟩ := Finset.exists_min_image s
      (fun j => x j / (-d j)) hs
    have hdj₀ : d j₀ < 0 := (Finset.mem_filter.mp hj₀s).2
    have hxj₀ : 0 < x j₀ := by
      have hxnonneg := hx.2 j₀
      have hxne : x j₀ ≠ 0 := by
        intro hz
        exact (not_lt_of_ge (hsign j₀ hz)) hdj₀
      exact lt_of_le_of_ne hxnonneg (Ne.symm hxne)
    let t : ℝ := (x j₀ / (-d j₀)) / 2
    have ht : 0 < t := by
      dsimp [t]
      have hden₀ : 0 < -d j₀ := by linarith
      have : 0 < x j₀ / (-d j₀) := div_pos hxj₀ hden₀
      linarith
    refine ⟨t, ht, ?_⟩
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx.1, hAd, smul_zero, add_zero]
    · intro j
      by_cases hdj : d j < 0
      · have hjs : j ∈ s := by simp [s, hdj]
        have hratio := hj₀min j hjs
        have hden : 0 < -d j := by linarith
        have ht_le : t ≤ x j / (-d j) := by
          dsimp [t]
          have hden₀ : 0 < -d j₀ := by linarith
          have hratio₀ : 0 < x j₀ / (-d j₀) := div_pos hxj₀ hden₀
          linarith
        have hmul : t * (-d j) ≤ x j := (le_div_iff₀ hden).mp ht_le
        change 0 ≤ x j + t * d j
        linarith
      · change 0 ≤ x j + t * d j
        exact add_nonneg (hx.2 j) (mul_nonneg (le_of_lt ht) (le_of_not_gt hdj))
  · refine ⟨1, by norm_num, ?_⟩
    constructor
    · rw [Matrix.mulVec_add, Matrix.mulVec_smul, hx.1, hAd, smul_zero, add_zero]
    · intro j
      have hdj : 0 ≤ d j := by
        by_contra hneg
        exact hs ⟨j, by simp [s, lt_of_not_ge hneg]⟩
      change 0 ≤ x j + 1 * d j
      simpa using add_nonneg (hx.2 j) hdj

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (hA : LinearIndependent ℝ (fun i => A i))
    (B : Fin m ↪ Fin n) (hB : LinearOptimization.IsStdBasis A B)
    (x : Fin n → ℝ) (hx : x ∈ LinearOptimization.stdPolyhedron A b)
    (hxB : ∀ j ∉ Set.range B, x j = 0) :
    ((∀ j, 0 ≤ LinearOptimization.reducedCost A c B j) →
      LinearOptimization.IsLpOptimal c (LinearOptimization.stdPolyhedron A b) x) ∧
    (LinearOptimization.IsLpOptimal c (LinearOptimization.stdPolyhedron A b) x →
      ¬LinearOptimization.IsStdDegenerateBasicSolution A b x →
      ∀ j, 0 ≤ LinearOptimization.reducedCost A c B j) := by
  classical
  have hcols : LinearIndependent ℝ (LinearOptimization.basisMatrix A B).col := by
    simpa [Matrix.col, LinearOptimization.basisMatrix] using hB
  letI : Invertible (LinearOptimization.basisMatrix A B) :=
    (Matrix.linearIndependent_cols_iff_isUnit.mp hcols).invertible
  have hCset : LinearOptimization.constraintSet
      (LinearOptimization.stdFormSystem A b) = LinearOptimization.stdPolyhedron A b := by
    ext y
    constructor
    · intro hy
      constructor
      · funext i
        simpa [LinearOptimization.stdFormSystem,
          LinearOptimization.LinearConstraint.IsSatisfiedAt] using hy (Sum.inl i)
      · intro j
        simpa [LinearOptimization.stdFormSystem,
          LinearOptimization.LinearConstraint.IsSatisfiedAt, dotProduct,
          Pi.single_apply] using hy (Sum.inr j)
    · rintro ⟨hAy, hynonneg⟩ q
      rcases q with i | j
      · simpa [LinearOptimization.stdFormSystem,
          LinearOptimization.LinearConstraint.IsSatisfiedAt] using congrFun hAy i
      · simpa [LinearOptimization.stdFormSystem,
          LinearOptimization.LinearConstraint.IsSatisfiedAt, dotProduct,
          Pi.single_apply] using hynonneg j
  have hext : x ∈ Set.extremePoints ℝ (LinearOptimization.stdPolyhedron A b) := by
    refine ⟨hx, ?_⟩
    intro y hy z hz hopen
    obtain ⟨a, d, ha, hd, had, hcomb⟩ := hopen
    have hyoff : ∀ j ∉ Set.range B, y j = 0 := by
      intro j hj
      have hxj := hxB j hj
      have hcj := congrFun hcomb j
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hcj
      have hyj : 0 ≤ y j := hy.2 j
      have hzj : 0 ≤ z j := hz.2 j
      rw [hxj] at hcj
      nlinarith
    have hker : A.mulVec (y - x) = 0 := by
      rw [Matrix.mulVec_sub, hy.1, hx.1, sub_self]
    have hoff : ∀ j ∉ Set.range B, (y - x) j = 0 := by
      intro j hj
      simp [hyoff j hj, hxB j hj]
    exact sub_eq_zero.mp (eq_zero_of_kernel_of_eq_zero_off_basis A B hB (y - x) hker hoff)
  have hbasic : LinearOptimization.IsBasicSolution
      (LinearOptimization.stdFormSystem A b) x := by
    have hneC : (LinearOptimization.constraintSet
        (LinearOptimization.stdFormSystem A b)).Nonempty := by
      rw [hCset]
      exact ⟨x, hx⟩
    have hxC : x ∈ LinearOptimization.constraintSet
        (LinearOptimization.stdFormSystem A b) := by simpa [hCset] using hx
    have hextC : x ∈ Set.extremePoints ℝ
        (LinearOptimization.constraintSet (LinearOptimization.stdFormSystem A b)) := by
      simpa [hCset] using hext
    have hbfs := ((LinearOptimization.lp_vertex_extreme_bfs_equiv
      (LinearOptimization.stdFormSystem A b) x hneC hxC).out 1 2).mp hextC
    exact hbfs.1
  constructor
  · intro hrc
    refine ⟨hx, ?_⟩
    intro y hy
    let d := y - x
    have hAd : A.mulVec d = 0 := by
      dsimp [d]
      rw [Matrix.mulVec_sub, hy.1, hx.1, sub_self]
    have hid := reducedCost_dot_kernel A c B hB d hAd
    have hnonneg : 0 ≤ LinearOptimization.reducedCost A c B ⬝ᵥ d := by
      apply Finset.sum_nonneg
      intro j _
      by_cases hj : j ∈ Set.range B
      · obtain ⟨i, rfl⟩ := hj
        rw [LinearOptimization.reducedCost_basic]
        simp
      · have hxj := hxB j hj
        have hyj := hy.2 j
        change 0 ≤ LinearOptimization.reducedCost A c B j * (y j - x j)
        rw [hxj, sub_zero]
        exact mul_nonneg (hrc j) hyj
    have hid' : LinearOptimization.reducedCost A c B ⬝ᵥ d =
        c ⬝ᵥ y - c ⬝ᵥ x := by
      rw [hid]
      dsimp [d]
      rw [dotProduct_sub]
    rw [hid'] at hnonneg
    exact sub_nonneg.mp hnonneg
  · intro hopt hnd j
    have hbasicPos : ∀ i : Fin m, 0 < x (B i) := by
      intro i
      have hxnonneg := hx.2 (B i)
      apply lt_of_le_of_ne hxnonneg
      intro hzero
      apply hnd
      refine ⟨hbasic, ?_⟩
      let R : Set (Fin n) := Set.range B
      let Z : Set (Fin n) := {j | x j = 0}
      have hsub : Rᶜ ⊆ Z := by
        intro q hq
        exact hxB q hq
      have hproper : Rᶜ ⊂ Z := by
        apply Set.ssubset_iff_subset_ne.mpr
        refine ⟨hsub, ?_⟩
        intro heq
        have hBiZ : B i ∈ Z := hzero.symm
        have hBiComp : B i ∈ Rᶜ := heq ▸ hBiZ
        exact hBiComp ⟨i, rfl⟩
      have hcard := Set.ncard_lt_ncard hproper
      have hRcard : R.ncard = m := by
        simpa [R] using Set.ncard_range_of_injective B.injective
      have hcompcard : Rᶜ.ncard = n - m := by
        rw [Set.ncard_compl R, hRcard]
        simp
      simpa [Z, hcompcard] using hcard
    by_contra hrc
    have hrcneg : LinearOptimization.reducedCost A c B j < 0 := lt_of_not_ge hrc
    have hjnot : j ∉ Set.range B := by
      intro hj
      obtain ⟨i, rfl⟩ := hj
      rw [LinearOptimization.reducedCost_basic] at hrcneg
      linarith
    let u : Fin m → ℝ :=
      (LinearOptimization.basisMatrix A B)⁻¹.mulVec (fun i ↦ A i j)
    have hMmul : (LinearOptimization.basisMatrix A B).mulVec u =
        (fun i ↦ A i j) := by
      dsimp [u]
      rw [Matrix.mulVec_mulVec, Matrix.mul_inv_of_invertible]
      simp
    let dir : Fin n → ℝ :=
      Pi.single j 1 - ∑ i : Fin m, u i • Pi.single (B i) 1
    have hdirKernel : A.mulVec dir = 0 := by
      funext row
      have hm := congrFun hMmul row
      simp only [LinearOptimization.basisMatrix, Matrix.mulVec, dotProduct,
        Matrix.submatrix_apply, Function.id_def] at hm
      dsimp [dir]
      simp only [Matrix.mulVec, dotProduct, Pi.sub_apply, Finset.sum_apply,
        Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      have hfirst : (∑ k : Fin n, A row k * (if k = j then 1 else 0)) = A row j := by
        simp
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hfirst]
      have hsecond :
          (∑ k : Fin n, A row k *
            (∑ i : Fin m, u i * if k = B i then 1 else 0)) =
          ∑ i : Fin m, A row (B i) * u i := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        simp
      rw [hsecond]
      linarith
    have hrcdir : LinearOptimization.reducedCost A c B ⬝ᵥ dir =
        LinearOptimization.reducedCost A c B j := by
      dsimp [dir]
      rw [dotProduct_sub, dotProduct_sum]
      simp only [dotProduct_smul, smul_eq_mul]
      rw [dotProduct_single]
      have hbasicZero : (∑ i : Fin m,
          u i * (LinearOptimization.reducedCost A c B ⬝ᵥ Pi.single (B i) 1)) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        rw [dotProduct_single, LinearOptimization.reducedCost_basic]
        ring
      rw [hbasicZero, sub_zero]
      ring
    have hdirCost : c ⬝ᵥ dir = LinearOptimization.reducedCost A c B j := by
      rw [← hrcdir]
      exact (reducedCost_dot_kernel A c B hB dir hdirKernel).symm
    have hsign : ∀ k, x k = 0 → 0 ≤ dir k := by
      intro k hxk
      have hknot : k ∉ Set.range B := by
        intro hk
        obtain ⟨i, rfl⟩ := hk
        have := hbasicPos i
        rw [hxk] at this
        linarith
      dsimp [dir]
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        Pi.single_apply]
      have hsumzero : (∑ i : Fin m, u i * if k = B i then 1 else 0) = 0 := by
        apply Finset.sum_eq_zero
        intro i _
        have hne : k ≠ B i := by
          intro heq
          apply hknot
          exact ⟨i, heq.symm⟩
        simp [hne]
      rw [hsumzero, sub_zero]
      split <;> norm_num
    obtain ⟨t, ht, hstep⟩ := feasible_step_of_tangent_std A b x dir hx hdirKernel hsign
    have hoptle := hopt.2 (x + t • dir) hstep
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul, hdirCost] at hoptle
    nlinarith
