-- Prove2me | solution 1 for LinearOptimization.network_basic_iff_tree
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T04:05:25.44574+00:00
-- url     : https://prove2.me/submissions/cf81ce0e-e6cb-4be9-8996-f228ac9fc092

import Definitions.Def_LinearOptimization_TreeSolution
import Definitions.Def_BasicSolution
import Theorems.Thm_LinearOptimization_network_incidence_rank
import Theorems.Thm_LinearOptimization_lp_standard_form_basic_iff
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Data.Fintype.EquivFin

open Matrix

private lemma networkAdjacentOn_symm {n m : ℕ}
    (arcs : Fin m → Fin n × Fin n) (T : Finset (Fin m)) :
    Symmetric (LinearOptimization.networkAdjacentOn arcs T) := by
  intro u v huv
  obtain ⟨k, hk, h | h⟩ := huv
  · exact ⟨k, hk, Or.inr h⟩
  · exact ⟨k, hk, Or.inl h⟩

private lemma truncated_weighted_sum {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1))
    (p : Fin (n + 1) → ℝ) (hlast : p (Fin.last n) = 0) (k : Fin m) :
    (∑ r : Fin n,
      p r.castSucc * LinearOptimization.truncatedIncidence arcs r k) =
      p (arcs k).1 - p (arcs k).2 := by
  unfold LinearOptimization.truncatedIncidence LinearOptimization.incidenceMatrix
  simp only [Matrix.submatrix_apply, Matrix.of_apply, Function.id_def]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · cases (arcs k).1 using Fin.lastCases with
    | last =>
        rw [hlast]
        apply Finset.sum_eq_zero
        intro r _
        simp [Ne.symm (Fin.castSucc_ne_last r)]
    | cast r => simp
  · cases (arcs k).2 using Fin.lastCases with
    | last =>
        rw [hlast]
        apply Finset.sum_eq_zero
        intro r _
        simp [Ne.symm (Fin.castSucc_ne_last r)]
    | cast r => simp

private lemma basis_range_is_tree {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1))
    (B : Fin n ↪ Fin m)
    (hB : LinearOptimization.IsStdBasis
      (LinearOptimization.truncatedIncidence arcs) B) :
    LinearOptimization.IsTreeArcSet arcs (Finset.univ.image B) := by
  classical
  let T : Finset (Fin m) := Finset.univ.image B
  have hcard : T.card + 1 = n + 1 := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ B.injective]
    simp
  refine ⟨hcard, ?_⟩
  intro u v
  by_contra huv
  have hadjSymm := networkAdjacentOn_symm arcs T
  have hclosureSymm : Symmetric
      (Relation.ReflTransGen (LinearOptimization.networkAdjacentOn arcs T)) :=
    Relation.ReflTransGen.symmetric hadjSymm
  have hq : ∃ q : Fin (n + 1),
      ¬Relation.ReflTransGen (LinearOptimization.networkAdjacentOn arcs T)
        q (Fin.last n) := by
    by_cases hu : Relation.ReflTransGen
        (LinearOptimization.networkAdjacentOn arcs T) u (Fin.last n)
    · refine ⟨v, ?_⟩
      intro hv
      exact huv (hu.trans (hclosureSymm hv))
    · exact ⟨u, hu⟩
  obtain ⟨q, hq⟩ := hq
  let p : Fin (n + 1) → ℝ := fun w =>
    if Relation.ReflTransGen (LinearOptimization.networkAdjacentOn arcs T) q w
      then 1 else 0
  have hplast : p (Fin.last n) = 0 := by simp [p, hq]
  have hpedge : ∀ a b,
      LinearOptimization.networkAdjacentOn arcs T a b → p a = p b := by
    intro a b hab
    have hab' := hadjSymm hab
    have hiff :
        Relation.ReflTransGen (LinearOptimization.networkAdjacentOn arcs T) q a ↔
        Relation.ReflTransGen (LinearOptimization.networkAdjacentOn arcs T) q b := by
      constructor
      · intro hqa
        exact hqa.tail hab
      · intro hqb
        exact hqb.tail hab'
    simp only [p]
    rw [if_congr hiff rfl rfl]
  have hcols : LinearIndependent ℝ
      ((LinearOptimization.basisMatrix
        (LinearOptimization.truncatedIncidence arcs) B).col) := by
    simpa [Matrix.col, LinearOptimization.basisMatrix] using hB
  have hunit : IsUnit (LinearOptimization.basisMatrix
      (LinearOptimization.truncatedIncidence arcs) B) :=
    Matrix.linearIndependent_cols_iff_isUnit.mp hcols
  have hrows : LinearIndependent ℝ
      (fun i => LinearOptimization.basisMatrix
        (LinearOptimization.truncatedIncidence arcs) B i) := by
    exact Matrix.linearIndependent_rows_iff_isUnit.mpr hunit
  have hzero : (∑ i : Fin n, p i.castSucc •
      LinearOptimization.basisMatrix
        (LinearOptimization.truncatedIncidence arcs) B i) = 0 := by
    funext r
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    change (∑ i : Fin n, p i.castSucc *
      LinearOptimization.truncatedIncidence arcs i (B r)) = 0
    rw [truncated_weighted_sum arcs p hplast (B r)]
    apply sub_eq_zero.mpr
    apply hpedge
    refine ⟨B r, ?_, Or.inl rfl⟩
    simp [T]
  have hcoeff := (Fintype.linearIndependent_iff.mp hrows)
    (fun i => p i.castSucc) hzero
  cases q using Fin.lastCases with
  | last => exact hq Relation.ReflTransGen.refl
  | cast i =>
      have hi := hcoeff i
      simp [p] at hi
      exact hi Relation.ReflTransGen.refl

private lemma basis_of_tree {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1))
    (hloop : LinearOptimization.HasNoSelfLoops arcs)
    (T : Finset (Fin m)) (hT : LinearOptimization.IsTreeArcSet arcs T) :
    ∃ B : Fin n ↪ Fin m,
      Set.range B = {k : Fin m | k ∈ T} ∧
      LinearOptimization.IsStdBasis
        (LinearOptimization.truncatedIncidence arcs) B := by
  classical
  have hcardT : T.card = n := Nat.add_right_cancel hT.1
  let e : Fin n ≃ T := Fintype.equivOfCardEq (by simp [hcardT])
  let B : Fin n ↪ Fin m :=
    ⟨fun r => (e r).1, fun _ _ h => e.injective (Subtype.ext h)⟩
  let subarcs : Fin n → Fin (n + 1) × Fin (n + 1) := fun r => arcs (B r)
  have hsubloop : LinearOptimization.HasNoSelfLoops subarcs := by
    intro r
    exact hloop (B r)
  have hsubconn : LinearOptimization.IsConnectedNetwork subarcs := by
    intro u v
    exact Relation.ReflTransGen.mono (fun a b hab => by
      obtain ⟨k, hkT, hk⟩ := hab
      let r : Fin n := e.symm ⟨k, hkT⟩
      refine ⟨r, ?_⟩
      simpa [subarcs, B, r] using hk) (hT.2 u v)
  have hrank := LinearOptimization.network_incidence_rank
    subarcs hsubloop hsubconn
  have hmatrix :
      (LinearOptimization.truncatedIncidence arcs).submatrix id B =
        LinearOptimization.truncatedIncidence subarcs := by
    ext i r
    rfl
  have hunit : IsUnit
      ((LinearOptimization.truncatedIncidence arcs).submatrix id B) := by
    rw [hmatrix]
    exact Matrix.linearIndependent_rows_iff_isUnit.mp (by
      simpa [Matrix.row] using hrank)
  have hB : LinearOptimization.IsStdBasis
      (LinearOptimization.truncatedIncidence arcs) B := by
    have hcols := Matrix.linearIndependent_cols_iff_isUnit.mpr hunit
    simpa [Matrix.col, LinearOptimization.IsStdBasis,
      LinearOptimization.basisMatrix] using hcols
  refine ⟨B, ?_, hB⟩
  ext k
  constructor
  · rintro ⟨r, rfl⟩
    exact (e r).2
  · intro hk
    refine ⟨e.symm ⟨k, hk⟩, ?_⟩
    simp [B]

theorem solution {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1))
    (bsupply : Fin (n + 1) → ℝ)
    (hloop : LinearOptimization.HasNoSelfLoops arcs)
    (hconn : LinearOptimization.IsConnectedNetwork arcs)
    (hsum : ∑ i, bsupply i = 0) (f : Fin m → ℝ) :
    LinearOptimization.IsBasicSolution
        (LinearOptimization.stdFormSystem
          (LinearOptimization.truncatedIncidence arcs)
          (LinearOptimization.truncatedSupply bsupply)) f ↔
      LinearOptimization.IsTreeSolution arcs bsupply f := by
  classical
  have hA := LinearOptimization.network_incidence_rank arcs hloop hconn
  constructor
  · intro hf
    obtain ⟨hAf, B, hB, hfB⟩ :=
      (LinearOptimization.lp_standard_form_basic_iff
        (LinearOptimization.truncatedIncidence arcs)
        (LinearOptimization.truncatedSupply bsupply) hA f).mp hf
    let T : Finset (Fin m) := Finset.univ.image B
    have hT : LinearOptimization.IsTreeArcSet arcs T := by
      simpa [T] using basis_range_is_tree arcs B hB
    refine ⟨T, hT, ?_, hAf⟩
    intro k hk
    apply hfB k
    simpa [T] using hk
  · rintro ⟨T, hT, hfT, hAf⟩
    obtain ⟨B, hRange, hB⟩ := basis_of_tree arcs hloop T hT
    apply (LinearOptimization.lp_standard_form_basic_iff
      (LinearOptimization.truncatedIncidence arcs)
      (LinearOptimization.truncatedSupply bsupply) hA f).mpr
    refine ⟨hAf, B, hB, ?_⟩
    intro k hk
    apply hfT k
    simpa [hRange] using hk
