-- Prove2me | solution 1 for LinearOptimization.lp_bfs_integer_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-10T02:30:29.378022+00:00
-- url     : https://prove2.me/submissions/ed77b090-592d-4170-b4e3-871d3b7b187d

import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

open Matrix
open LinearOptimization

private theorem standard_support_columns_linearIndependent {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (x : Fin n → ℝ)
    (hx : x ∈ Set.extremePoints ℝ
      (stdPolyhedron (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ)))) :
    LinearIndependent ℝ
      (fun j : {j : Fin n // x j ≠ 0} =>
        (A.map ((↑) : ℤ → ℝ))ᵀ j.1) := by
  classical
  let Ar : Matrix (Fin m) (Fin n) ℝ := A.map ((↑) : ℤ → ℝ)
  let br : Fin m → ℝ := fun i => (b i : ℝ)
  let C := stdFormSystem Ar br
  have hset : constraintSet C = stdPolyhedron Ar br := by
    ext y
    simp only [constraintSet, Set.mem_setOf_eq, stdPolyhedron]
    constructor
    · intro hy
      constructor
      · ext i
        simpa [C, stdFormSystem, LinearConstraint.IsSatisfiedAt,
          dotProduct, mulVec] using hy (Sum.inl i)
      · intro j
        have hj := hy (Sum.inr j)
        change 0 ≤ Pi.single j 1 ⬝ᵥ y at hj
        simpa using hj
    · rintro ⟨hAy, hy0⟩ i
      cases i with
      | inl i =>
          simpa [C, stdFormSystem, LinearConstraint.IsSatisfiedAt,
            dotProduct, mulVec] using congrFun hAy i
      | inr j =>
          change LinearConstraint.IsSatisfiedAt ⟨Pi.single j 1, 0, .ge⟩ y
          change 0 ≤ Pi.single j 1 ⬝ᵥ y
          simpa using hy0 j
  have hxC : x ∈ constraintSet C := by
    apply extremePoints_subset at hx
    simpa [hset, Ar, br] using hx
  have hxextC : x ∈ Set.extremePoints ℝ (constraintSet C) := by
    simpa [hset, Ar, br] using hx
  have ht := lp_vertex_extreme_bfs_equiv C x ⟨x, hxC⟩ hxC
  have hbfs : IsBasicFeasibleSolution C x := (ht.out 1 2).mp hxextC
  rcases hbfs.1.2 with ⟨s, hs_card, hs_active, hs_li⟩
  let e : Fin n ≃ s := Fintype.equivOfCardEq (by simp [hs_card])
  let Q : Matrix (Fin n) (Fin n) ℝ := fun i => (C (e i)).a
  have hQli : LinearIndependent ℝ (fun i => Q i) := by
    simpa [Q] using hs_li.comp e e.injective
  have hQunit : IsUnit Q := Matrix.linearIndependent_rows_iff_isUnit.mp hQli
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  let d : Fin n → ℝ := fun k => if hk : x k ≠ 0 then g ⟨k, hk⟩ else 0
  have hAd : Ar.mulVec d = 0 := by
    ext i
    have hi := congrFun hg i
    change (∑ k, Ar i k * d k) = 0
    calc
      (∑ k, Ar i k * d k) =
          Finset.sum (Finset.univ.filter (fun k => x k ≠ 0))
            (fun k => Ar i k * d k) := by
        symm
        apply Finset.sum_subset (by simp)
        intro k _ hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hk
        simp [d, hk]
      _ = ∑ k : {k : Fin n // x k ≠ 0}, Ar i k.1 * d k.1 := by
        rw [Finset.sum_subtype (Finset.univ.filter (fun k => x k ≠ 0))]
        simp
      _ = ∑ k : {k : Fin n // x k ≠ 0}, g k * Ar i k.1 := by
        apply Finset.sum_congr rfl
        intro k _
        simp [d, k.property, mul_comm]
      _ = 0 := by
        simpa [Ar, Matrix.transpose_apply] using hi
  have hQd : Q.mulVec d = 0 := by
    ext i
    have hi_active := hs_active (e i) (e i).property
    rcases hci : (e i : Fin m ⊕ Fin n) with p | q
    · have hip := congrFun hAd p
      simpa [Q, C, stdFormSystem, hci, Matrix.mulVec, dotProduct] using hip
    · have hxq : x q = 0 := by
        have hh : Pi.single q 1 ⬝ᵥ x = 0 := by
          simpa only [LinearConstraint.IsActiveAt, C, stdFormSystem, hci] using hi_active
        simpa using hh
      change (C (e i)).a ⬝ᵥ d = 0
      rw [hci]
      simp [C, stdFormSystem, d, hxq]
  have hd0 : d = 0 := by
    have h := congrArg (Q⁻¹.mulVec) hQd
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul Q
      ((Matrix.isUnit_iff_isUnit_det Q).mp hQunit)] at h
    simpa using h
  have := congrFun hd0 j
  simpa [d, j.property] using this

private theorem exists_support_row_embedding {m n : ℕ}
    (Ar : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ)
    (hcols : LinearIndependent ℝ
      (fun j : {j : Fin n // x j ≠ 0} => Arᵀ j.1)) :
    ∃ r : {j : Fin n // x j ≠ 0} ↪ Fin m,
      IsUnit (Matrix.det ((fun i j => Ar (r i) j.1) :
        Matrix {j : Fin n // x j ≠ 0} {j : Fin n // x j ≠ 0} ℝ)) := by
  classical
  let S := {j : Fin n // x j ≠ 0}
  let C : Matrix (Fin m) S ℝ := fun i j => Ar i j.1
  have hCcols : LinearIndependent ℝ C.col := by
    simpa [C, S, Matrix.col, Matrix.transpose_apply] using hcols
  have hCrank : C.rank = Fintype.card S := by
    rw [Matrix.rank_eq_finrank_span_cols,
      linearIndependent_iff_card_eq_finrank_span.mp hCcols, Set.finrank]
  have hrowfin : Module.finrank ℝ (Submodule.span ℝ (Set.range C.row)) =
      Fintype.card S := by
    rw [← Matrix.rank_eq_finrank_span_row, hCrank]
  have hrowtop : Submodule.span ℝ (Set.range C.row) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [hrowfin, Module.finrank_fintype_fun_eq_card]
  rcases Submodule.exists_finset_span_eq_linearIndepOn ℝ (Set.range C.row) with
    ⟨t, ht_sub, ht_card, ht_span, ht_indep⟩
  have ht_card_S : t.card = Fintype.card S := by
    rw [ht_card, hrowtop, finrank_top, Module.finrank_fintype_fun_eq_card]
  let e : S ≃ t := Fintype.equivOfCardEq (by simp [ht_card_S])
  have ht_range (v : t) : (v.1 : S → ℝ) ∈ Set.range C.row :=
    ht_sub v.property
  let pick : t → Fin m := fun v => Classical.choose (ht_range v)
  have hpick (v : t) : C.row (pick v) = v.1 :=
    Classical.choose_spec (ht_range v)
  have hpick_inj : Function.Injective pick := by
    intro v w hvw
    apply Subtype.ext
    rw [← hpick v, ← hpick w, hvw]
  let r : S ↪ Fin m :=
    ⟨fun j => pick (e j), fun i j hij => e.injective (hpick_inj hij)⟩
  let B : Matrix S S ℝ := fun i j => Ar (r i) j.1
  have htli : LinearIndependent ℝ (fun v : t => (v.1 : S → ℝ)) :=
    ht_indep.linearIndependent
  have hcomp := htli.comp e e.injective
  have hBli : LinearIndependent ℝ B.row := by
    have hfun : B.row = (fun v : t => (v.1 : S → ℝ)) ∘ e := by
      funext i j
      change Ar (pick (e i)) j.1 = (e i).1 j
      exact congrFun (hpick (e i)) j
    rw [hfun]
    exact hcomp
  refine ⟨r, ?_⟩
  have hBunit : IsUnit B := Matrix.linearIndependent_rows_iff_isUnit.mp hBli
  simpa [B, S] using (Matrix.isUnit_iff_isUnit_det B).mp hBunit

private theorem general_extreme_coordinate_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (U : ℤ)
    (hA : ∀ i j, |A i j| ≤ U) (hb : ∀ i, |b i| ≤ U)
    (x : Fin n → ℝ)
    (hx : x ∈ Set.extremePoints ℝ
      (polyhedron (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))))
    (j : Fin n) :
    |x j| ≤ ((n : ℝ) * (U : ℝ)) ^ n := by
  classical
  let Ar : Matrix (Fin m) (Fin n) ℝ := A.map ((↑) : ℤ → ℝ)
  let br : Fin m → ℝ := fun i => (b i : ℝ)
  let C := generalFormSystem Ar br
  have hset : constraintSet C = polyhedron Ar br := by
    rfl
  have hxP : x ∈ polyhedron Ar br := extremePoints_subset hx
  have hxC : x ∈ constraintSet C := by simpa [hset]
  have hxextC : x ∈ Set.extremePoints ℝ (constraintSet C) := by
    simpa [hset, Ar, br] using hx
  have ht := lp_vertex_extreme_bfs_equiv C x ⟨x, hxC⟩ hxC
  have hbfs : IsBasicFeasibleSolution C x := (ht.out 1 2).mp hxextC
  rcases hbfs.1.2 with ⟨s, hs_card, hs_active, hs_li⟩
  let e : Fin n ≃ s := Fintype.equivOfCardEq (by simp [hs_card])
  let Bz : Matrix (Fin n) (Fin n) ℤ := fun i k => A (e i) k
  let cz : Fin n → ℤ := fun i => b (e i)
  let B : Matrix (Fin n) (Fin n) ℝ := Bz.map ((↑) : ℤ → ℝ)
  let c : Fin n → ℝ := fun i => (cz i : ℝ)
  have hB_li : LinearIndependent ℝ (fun i => B i) := by
    have hcomp := hs_li.comp e e.injective
    simpa [B, Bz, C, generalFormSystem, Ar] using hcomp
  have hBunitM : IsUnit B := Matrix.linearIndependent_rows_iff_isUnit.mp hB_li
  have hBunit : IsUnit B.det := (Matrix.isUnit_iff_isUnit_det B).mp hBunitM
  have hBx : B.mulVec x = c := by
    ext i
    have hi := hs_active (e i) (e i).property
    simpa [LinearConstraint.IsActiveAt, C, generalFormSystem, Ar, B, Bz, c, cz,
      dotProduct, mulVec] using hi
  have hxinv : x = B⁻¹.mulVec c := by
    have h := congrArg (B⁻¹.mulVec) hBx
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hBunit] at h
    simpa using h
  have hcramer : B.det * x j = (B.updateCol j c).det := by
    have h := congrFun (B.det_smul_inv_mulVec_eq_cramer c hBunit) j
    rw [← hxinv, Matrix.cramer_apply] at h
    simpa using h
  have hBzdet0 : Bz.det ≠ 0 := by
    intro hzero
    have hcast : B.det = (Bz.det : ℝ) := by
      change ((Int.castRingHom ℝ).mapMatrix Bz).det = (Bz.det : ℝ)
      rw [← RingHom.map_det]
      rfl
    have : B.det = 0 := by rw [hcast, hzero]; simp
    exact hBunit.ne_zero this
  have hdet_lower : (1 : ℝ) ≤ |B.det| := by
    rw [show B.det = (Bz.det : ℝ) by
      change ((Int.castRingHom ℝ).mapMatrix Bz).det = (Bz.det : ℝ)
      rw [← RingHom.map_det]
      rfl]
    rw [← Int.cast_abs]
    exact_mod_cast (Int.one_le_abs hBzdet0)
  let Mz : Matrix (Fin n) (Fin n) ℤ := Bz.updateCol j cz
  let M : Matrix (Fin n) (Fin n) ℝ := Mz.map ((↑) : ℤ → ℝ)
  have hM_eq : M = B.updateCol j c := by
    ext i k
    by_cases hkj : k = j
    · subst k
      simp [M, Mz, B, c, cz]
    · simp [M, Mz, B, c, cz, hkj]
  have hU0 : 0 ≤ U := by
    have := hA (e j) j
    exact (abs_nonneg _).trans this
  have hMentry : ∀ i k, |(M i k)| ≤ (U : ℝ) := by
    intro i k
    by_cases hkj : k = j
    · subst k
      simp only [M, Mz, Matrix.map_apply, Matrix.updateCol_self, cz]
      exact_mod_cast hb (e i)
    · simp only [M, Mz, Matrix.map_apply, Matrix.updateCol_ne hkj, Bz]
      exact_mod_cast hA (e i) k
  have hMdet : |M.det| ≤ (n.factorial : ℝ) * (U : ℝ) ^ n := by
    simpa [Fintype.card_fin, nsmul_eq_mul] using
      (Matrix.det_le (A := M) (abv := (AbsoluteValue.abs : AbsoluteValue ℝ ℝ)) hMentry)
  have hfac : (n.factorial : ℝ) * (U : ℝ) ^ n ≤
      ((n : ℝ) * (U : ℝ)) ^ n := by
    rw [mul_pow]
    gcongr
    exact_mod_cast n.factorial_le_pow
  have hnum : |(B.updateCol j c).det| ≤ ((n : ℝ) * (U : ℝ)) ^ n := by
    rw [← hM_eq]
    exact hMdet.trans hfac
  calc
    |x j| = 1 * |x j| := by ring
    _ ≤ |B.det| * |x j| :=
      mul_le_mul_of_nonneg_right hdet_lower (abs_nonneg _)
    _ = |B.det * x j| := (abs_mul _ _).symm
    _ = |(B.updateCol j c).det| := by rw [hcramer]
    _ ≤ ((n : ℝ) * (U : ℝ)) ^ n := hnum

private theorem standard_extreme_coordinate_bound {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (U : ℤ)
    (hA : ∀ i j, |A i j| ≤ U) (hb : ∀ i, |b i| ≤ U)
    (x : Fin n → ℝ)
    (hx : x ∈ Set.extremePoints ℝ
      (stdPolyhedron (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))))
    (j : Fin n) :
    |x j| ≤ ((m : ℝ) * (U : ℝ)) ^ m := by
  classical
  let Ar : Matrix (Fin m) (Fin n) ℝ := A.map ((↑) : ℤ → ℝ)
  have hRHS0 : 0 ≤ ((m : ℝ) * (U : ℝ)) ^ m := by
    cases m with
    | zero => norm_num
    | succ m =>
        have hU0z : 0 ≤ U := (abs_nonneg (A (0 : Fin (m + 1)) j)).trans (hA 0 j)
        positivity
  by_cases hj : x j = 0
  · simp [hj, hRHS0]
  let S := {k : Fin n // x k ≠ 0}
  let jj : S := ⟨j, hj⟩
  haveI : Nonempty S := ⟨jj⟩
  have hcols := standard_support_columns_linearIndependent A b x hx
  rcases exists_support_row_embedding Ar x (by simpa [Ar, S] using hcols) with
    ⟨r, hBunit⟩
  let Bz : Matrix S S ℤ := fun i k => A (r i) k.1
  let B : Matrix S S ℝ := Bz.map ((↑) : ℤ → ℝ)
  let cz : S → ℤ := fun i => b (r i)
  let c : S → ℝ := fun i => (cz i : ℝ)
  let xs : S → ℝ := fun k => x k.1
  have hBunit' : IsUnit B.det := by
    simpa [B, Bz, Ar, S] using hBunit
  have hxP : x ∈ stdPolyhedron Ar (fun i => (b i : ℝ)) := by
    have := extremePoints_subset hx
    simpa [Ar] using this
  have hBx : B.mulVec xs = c := by
    ext i
    have hi := congrFun hxP.1 (r i)
    have hrestrict : (∑ k : Fin n, Ar (r i) k * x k) =
        ∑ k : S, Ar (r i) k.1 * x k.1 := by
      calc
        (∑ k : Fin n, Ar (r i) k * x k) =
            Finset.sum (Finset.univ.filter (fun k : Fin n => x k ≠ 0))
              (fun k => Ar (r i) k * x k) := by
          symm
          apply Finset.sum_subset (Finset.filter_subset _ _)
          intro k _ hk
          have hk0 : x k = 0 := by simpa using hk
          simp [hk0]
        _ = ∑ k : S, Ar (r i) k.1 * x k.1 := by
          exact Finset.sum_subtype
            (Finset.univ.filter (fun k : Fin n => x k ≠ 0)) (by simp)
            (fun k => Ar (r i) k * x k)
    change (∑ k : S, B i k * xs k) = c i
    calc
      (∑ k : S, B i k * xs k) = ∑ k : S, Ar (r i) k.1 * x k.1 := by
        apply Finset.sum_congr rfl
        intro k _
        simp [B, Bz, xs, Ar, S]
      _ = ∑ k : Fin n, Ar (r i) k * x k := hrestrict.symm
      _ = c i := by
        simpa [Ar, Matrix.mulVec, dotProduct, c, cz] using hi
  have hxinv : xs = B⁻¹.mulVec c := by
    have h := congrArg (B⁻¹.mulVec) hBx
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul B hBunit'] at h
    simpa using h
  have hcramer : B.det * xs jj = (B.updateCol jj c).det := by
    have h := congrFun (B.det_smul_inv_mulVec_eq_cramer c hBunit') jj
    rw [← hxinv, Matrix.cramer_apply] at h
    simpa using h
  have hBzdet0 : Bz.det ≠ 0 := by
    intro hzero
    have hcast : B.det = (Bz.det : ℝ) := by
      change ((Int.castRingHom ℝ).mapMatrix Bz).det = (Bz.det : ℝ)
      rw [← RingHom.map_det]
      rfl
    have : B.det = 0 := by rw [hcast, hzero]; simp
    exact hBunit'.ne_zero this
  have hdet_lower : (1 : ℝ) ≤ |B.det| := by
    rw [show B.det = (Bz.det : ℝ) by
      change ((Int.castRingHom ℝ).mapMatrix Bz).det = (Bz.det : ℝ)
      rw [← RingHom.map_det]
      rfl]
    rw [← Int.cast_abs]
    exact_mod_cast (Int.one_le_abs hBzdet0)
  have hU0z : 0 ≤ U := (abs_nonneg (A (r jj) j)).trans (hA (r jj) j)
  have hUne : U ≠ 0 := by
    intro hUz
    have hBzero : B = 0 := by
      ext i k
      have hik := hA (r i) k.1
      rw [hUz] at hik
      have hz : A (r i) k.1 = 0 := abs_eq_zero.mp (le_antisymm hik (abs_nonneg _))
      simp [B, Bz, hz]
    apply hBunit'.ne_zero
    rw [hBzero, Matrix.det_zero ⟨jj⟩]
  have hU1z : 1 ≤ U := by omega
  let Mz : Matrix S S ℤ := Bz.updateCol jj cz
  let M : Matrix S S ℝ := Mz.map ((↑) : ℤ → ℝ)
  have hM_eq : M = B.updateCol jj c := by
    ext i k
    by_cases hkj : k = jj
    · subst k
      simp [M, Mz, B, c, cz]
    · simp [M, Mz, B, c, cz, hkj]
  have hMentry : ∀ i k, |M i k| ≤ (U : ℝ) := by
    intro i k
    by_cases hkj : k = jj
    · subst k
      simp only [M, Mz, Matrix.map_apply, Matrix.updateCol_self, cz]
      exact_mod_cast hb (r i)
    · simp only [M, Mz, Matrix.map_apply, Matrix.updateCol_ne hkj, Bz]
      exact_mod_cast hA (r i) k.1
  let k := Fintype.card S
  have hk_le_m : k ≤ m := by
    simpa [k, S] using Fintype.card_le_of_injective r r.injective
  have hk_pos : 0 < k := by
    have : Nonempty S := ⟨jj⟩
    exact Fintype.card_pos
  have hMdet : |M.det| ≤ (k.factorial : ℝ) * (U : ℝ) ^ k := by
    simpa [k, nsmul_eq_mul] using
      (Matrix.det_le (A := M) (abv := (AbsoluteValue.abs : AbsoluteValue ℝ ℝ)) hMentry)
  have hfac : (k.factorial : ℝ) * (U : ℝ) ^ k ≤
      ((k : ℝ) * (U : ℝ)) ^ k := by
    rw [mul_pow]
    gcongr
    exact_mod_cast k.factorial_le_pow
  have hbase : (0 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU0z
  have hkm_base : (k : ℝ) * (U : ℝ) ≤ (m : ℝ) * (U : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hbase
    exact_mod_cast hk_le_m
  have hmU1 : (1 : ℝ) ≤ (m : ℝ) * (U : ℝ) := by
    have hm1 : 1 ≤ m := le_trans (Nat.succ_le_iff.mp hk_pos) hk_le_m
    have hm1r : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
    have hU1 : (1 : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU1z
    nlinarith
  have hpow : ((k : ℝ) * (U : ℝ)) ^ k ≤
      ((m : ℝ) * (U : ℝ)) ^ m := by
    calc
      ((k : ℝ) * (U : ℝ)) ^ k ≤ ((m : ℝ) * (U : ℝ)) ^ k := by
        exact pow_le_pow_left₀ (mul_nonneg (by positivity) hbase) hkm_base k
      _ ≤ ((m : ℝ) * (U : ℝ)) ^ m := pow_le_pow_right₀ hmU1 hk_le_m
  have hnum : |(B.updateCol jj c).det| ≤ ((m : ℝ) * (U : ℝ)) ^ m := by
    rw [← hM_eq]
    exact hMdet.trans (hfac.trans hpow)
  calc
    |x j| = |xs jj| := rfl
    _ = 1 * |xs jj| := by ring
    _ ≤ |B.det| * |xs jj| :=
      mul_le_mul_of_nonneg_right hdet_lower (abs_nonneg _)
    _ = |B.det * xs jj| := (abs_mul _ _).symm
    _ = |(B.updateCol jj c).det| := by rw [hcramer]
    _ ≤ ((m : ℝ) * (U : ℝ)) ^ m := hnum

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ) (U : ℤ)
    (hA : ∀ i j, |A i j| ≤ U) (hb : ∀ i, |b i| ≤ U) :
    (∀ x ∈ Set.extremePoints ℝ
        (polyhedron (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))),
      ∀ j, -(((n : ℝ) * (U : ℝ)) ^ n) ≤ x j ∧
        x j ≤ ((n : ℝ) * (U : ℝ)) ^ n) ∧
    (∀ x ∈ Set.extremePoints ℝ
        (stdPolyhedron (A.map ((↑) : ℤ → ℝ)) (fun i => (b i : ℝ))),
      ∀ j, -(((m : ℝ) * (U : ℝ)) ^ m) ≤ x j ∧
        x j ≤ ((m : ℝ) * (U : ℝ)) ^ m) := by
  constructor
  · intro x hx j
    exact abs_le.mp (general_extreme_coordinate_bound A b U hA hb x hx j)
  · intro x hx j
    exact abs_le.mp (standard_extreme_coordinate_bound A b U hA hb x hx j)
