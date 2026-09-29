-- Prove2me | solution 1 for LinearOptimization.network_integer_optimum_exists
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-06T04:31:33.313119+00:00
-- url     : https://prove2.me/submissions/78cb096d-4e0c-4350-acdc-4e02736c06ab

import Definitions.Def_LinearOptimization_NetworkFlowProblem
import Definitions.Def_BasicSolution
import Definitions.Def_LinearOptimization_DualLP
import Theorems.Thm_LinearOptimization_network_flow_integrality
import Theorems.Thm_LinearOptimization_network_incidence_rank
import Theorems.Thm_LinearOptimization_lp_standard_form_basic_iff
import Theorems.Thm_LinearOptimization_polyhedron_std_form_has_bfs
import Theorems.Thm_LinearOptimization_lp_attains_or_unbounded
import Theorems.Thm_LinearOptimization_lp_optimal_extreme_point
import Theorems.Thm_LinearOptimization_lp_vertex_extreme_bfs_equiv
import Theorems.Thm_LinearOptimization_lp_strong_duality
import Theorems.Thm_LinearOptimization_polyhedron_extreme_point_existence
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fin.Basic

open Matrix

private def stdRowEquiv (r s : ℕ) :
    Fin (r + r + s) ≃ (Fin r ⊕ Fin r) ⊕ Fin s :=
  finSumFinEquiv.symm.trans (Equiv.sumCongr finSumFinEquiv.symm (Equiv.refl _))

private def stdAsGeneralMatrix {r s : ℕ} (A : Matrix (Fin r) (Fin s) ℝ) :
    Matrix (Fin (r + r + s)) (Fin s) ℝ :=
  fun q ↦ match stdRowEquiv r s q with
  | .inl (.inl i) => A i
  | .inl (.inr i) => -A i
  | .inr j => Pi.single j 1

private def stdAsGeneralRhs {r s : ℕ} (b : Fin r → ℝ) :
    Fin (r + r + s) → ℝ :=
  fun q ↦ match stdRowEquiv r s q with
  | .inl (.inl i) => b i
  | .inl (.inr i) => -b i
  | .inr _ => 0

private lemma stdPolyhedron_eq_general {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) ℝ) (b : Fin r → ℝ) :
    LinearOptimization.stdPolyhedron A b =
      LinearOptimization.polyhedron (stdAsGeneralMatrix A) (stdAsGeneralRhs b) := by
  ext x
  constructor
  · rintro ⟨hAx, hx⟩ q
    cases hq : stdRowEquiv r s q with
    | inl z =>
        cases z with
        | inl i =>
            simpa [stdAsGeneralMatrix, stdAsGeneralRhs, hq,
              Matrix.mulVec, dotProduct] using le_of_eq (congrFun hAx i).symm
        | inr i =>
            have hi := congrFun hAx i
            have hi' : A i ⬝ᵥ x = b i := by
              simpa [Matrix.mulVec] using hi
            simp only [stdAsGeneralMatrix, stdAsGeneralRhs, hq, Matrix.mulVec]
            change -b i ≤ (-A i) ⬝ᵥ x
            rw [neg_dotProduct, hi']
    | inr j =>
        have hj : 0 ≤ Pi.single j (1 : ℝ) ⬝ᵥ x := by simpa using hx j
        simpa only [stdAsGeneralMatrix, stdAsGeneralRhs, hq,
          Matrix.mulVec] using hj
  · intro hx
    refine ⟨?_, ?_⟩
    · funext i
      have hle := hx ((stdRowEquiv r s).symm (.inl (.inl i)))
      have hge := hx ((stdRowEquiv r s).symm (.inl (.inr i)))
      have hle' : b i ≤ (A.mulVec x) i := by
        simpa [stdAsGeneralMatrix, stdAsGeneralRhs, Matrix.mulVec] using hle
      have hge' : (A.mulVec x) i ≤ b i := by
        simp only [stdAsGeneralMatrix, stdAsGeneralRhs,
          Equiv.apply_symm_apply, Matrix.mulVec] at hge
        change -b i ≤ (-A i) ⬝ᵥ x at hge
        rw [neg_dotProduct] at hge
        simpa [Matrix.mulVec] using (neg_le_neg_iff.mp hge)
      exact le_antisymm hge' hle'
    · intro j
      have hj := hx ((stdRowEquiv r s).symm (.inr j))
      have hj' : 0 ≤ Pi.single j (1 : ℝ) ⬝ᵥ x := by
        simpa only [stdAsGeneralMatrix, stdAsGeneralRhs,
          Equiv.apply_symm_apply, Matrix.mulVec] using hj
      simpa using hj'

private lemma constraintSet_std_eq {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) ℝ) (b : Fin r → ℝ) :
    LinearOptimization.constraintSet (LinearOptimization.stdFormSystem A b) =
      LinearOptimization.stdPolyhedron A b := by
  ext x
  constructor
  · intro hx
    refine ⟨?_, ?_⟩
    · funext i
      simpa [LinearOptimization.stdFormSystem,
        LinearOptimization.LinearConstraint.IsSatisfiedAt] using hx (.inl i)
    · intro j
      have hj := hx (.inr j)
      change 0 ≤ Pi.single j (1 : ℝ) ⬝ᵥ x at hj
      simpa using hj
  · rintro ⟨hAx, hx⟩ (i | j)
    · simpa [LinearOptimization.stdFormSystem,
        LinearOptimization.LinearConstraint.IsSatisfiedAt] using congrFun hAx i
    · simpa [LinearOptimization.stdFormSystem,
        LinearOptimization.LinearConstraint.IsSatisfiedAt] using
        (show 0 ≤ Pi.single j (1 : ℝ) ⬝ᵥ x by simpa using hx j)

private lemma constraintSet_general_eq {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) ℝ) (b : Fin r → ℝ) :
    LinearOptimization.constraintSet (LinearOptimization.generalFormSystem A b) =
      LinearOptimization.polyhedron A b := by
  ext x
  constructor
  · intro hx i
    simpa [LinearOptimization.generalFormSystem,
      LinearOptimization.LinearConstraint.IsSatisfiedAt] using hx i
  · intro hx i
    simpa [LinearOptimization.generalFormSystem,
      LinearOptimization.LinearConstraint.IsSatisfiedAt] using hx i

private lemma lpValue_ne_top_nonempty {s : ℕ}
    (c : Fin s → ℝ) (S : Set (Fin s → ℝ))
    (h : LinearOptimization.lpValue c S ≠ ⊤) : S.Nonempty := by
  by_contra hne
  have hempty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp hne
  apply h
  simp [LinearOptimization.lpValue, hempty]

private lemma finite_std_lp_has_optimal_basic {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) ℝ) (b : Fin r → ℝ) (c : Fin s → ℝ)
    (hfin : LinearOptimization.lpValue c (LinearOptimization.stdPolyhedron A b) ≠ ⊤ ∧
      LinearOptimization.lpValue c (LinearOptimization.stdPolyhedron A b) ≠ ⊥) :
    ∃ x, LinearOptimization.IsLpOptimal c
        (LinearOptimization.stdPolyhedron A b) x ∧
      LinearOptimization.IsBasicSolution (LinearOptimization.stdFormSystem A b) x := by
  let G := stdAsGeneralMatrix A
  let d : Fin (r + r + s) → ℝ := stdAsGeneralRhs (s := s) b
  have hSG : LinearOptimization.stdPolyhedron A b =
      LinearOptimization.polyhedron G d := by
    exact stdPolyhedron_eq_general A b
  have hneS : (LinearOptimization.stdPolyhedron A b).Nonempty :=
    lpValue_ne_top_nonempty c _ hfin.1
  have hneG : (LinearOptimization.polyhedron G d).Nonempty := by
    rw [← hSG]
    exact hneS
  obtain ⟨x₀, hx₀bfs⟩ :=
    (LinearOptimization.polyhedron_std_form_has_bfs A b).2 hneS
  have hCS : LinearOptimization.constraintSet
      (LinearOptimization.stdFormSystem A b) =
      LinearOptimization.stdPolyhedron A b := constraintSet_std_eq A b
  have hneC : (LinearOptimization.constraintSet
      (LinearOptimization.stdFormSystem A b)).Nonempty := by
    rw [hCS]
    exact hneS
  have hx₀extS : x₀ ∈ Set.extremePoints ℝ
      (LinearOptimization.stdPolyhedron A b) := by
    have ht := LinearOptimization.lp_vertex_extreme_bfs_equiv
      (LinearOptimization.stdFormSystem A b) x₀ hneC hx₀bfs.2
    have hextC := (ht.out 2 1).mp hx₀bfs
    rwa [hCS] at hextC
  have hextG : (Set.extremePoints ℝ
      (LinearOptimization.polyhedron G d)).Nonempty := by
    refine ⟨x₀, ?_⟩
    rwa [← hSG]
  have hoptG : ∃ x, LinearOptimization.IsLpOptimal c
      (LinearOptimization.polyhedron G d) x := by
    rcases LinearOptimization.lp_attains_or_unbounded G d c hneG with hbot | hopt
    · exfalso
      apply hfin.2
      rwa [hSG]
    · exact hopt
  obtain ⟨x, hxextG, hxoptG⟩ :=
    LinearOptimization.lp_optimal_extreme_point G d c hextG hoptG
  have hxextS : x ∈ Set.extremePoints ℝ
      (LinearOptimization.stdPolyhedron A b) := by
    rwa [hSG]
  have hxoptS : LinearOptimization.IsLpOptimal c
      (LinearOptimization.stdPolyhedron A b) x := by
    rwa [hSG]
  have hxmemC : x ∈ LinearOptimization.constraintSet
      (LinearOptimization.stdFormSystem A b) := by
    rw [hCS]
    exact hxoptS.1
  have ht := LinearOptimization.lp_vertex_extreme_bfs_equiv
    (LinearOptimization.stdFormSystem A b) x hneC hxmemC
  have hxbfs : LinearOptimization.IsBasicFeasibleSolution
      (LinearOptimization.stdFormSystem A b) x := by
    apply (ht.out 1 2).mp
    rwa [hCS]
  exact ⟨x, hxoptS, hxbfs.1⟩

private lemma dualFeasible_eq_polyhedron {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) ℝ) (c : Fin s → ℝ) :
    LinearOptimization.dualFeasibleStd A c =
      LinearOptimization.polyhedron (-Aᵀ) (-c) := by
  ext p
  constructor
  · intro hp j
    have hj := hp j
    change -c j ≤ (-Aᵀ).mulVec p j
    rw [Matrix.neg_mulVec]
    exact neg_le_neg hj
  · intro hp j
    have hj := hp j
    change -c j ≤ (-Aᵀ).mulVec p j at hj
    rw [Matrix.neg_mulVec] at hj
    exact (neg_le_neg_iff.mp hj)

private def standardLP {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) ℝ) (b : Fin r → ℝ) (c : Fin s → ℝ) :
    LinearOptimization.GeneralFormLP r s where
  A := A
  b := b
  c := c
  rowRel := fun _ ↦ .eq
  colSign := fun _ ↦ .nonneg

private lemma standardLP_feasible {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) ℝ) (b : Fin r → ℝ) (c : Fin s → ℝ) :
    LinearOptimization.generalFeasibleSet (standardLP A b c) =
      LinearOptimization.stdPolyhedron A b := by
  ext x
  simp only [standardLP, LinearOptimization.generalFeasibleSet,
    LinearOptimization.stdPolyhedron,
    LinearOptimization.LinearConstraint.IsSatisfiedAt,
    LinearOptimization.VarSign.IsSatisfiedBy, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hrow, hx⟩
    exact ⟨funext hrow, hx⟩
  · rintro ⟨hrow, hx⟩
    exact ⟨fun i ↦ congrFun hrow i, hx⟩

private lemma standardLP_dual_feasible {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) ℝ) (b : Fin r → ℝ) (c : Fin s → ℝ) :
    LinearOptimization.generalFeasibleSet
        (LinearOptimization.dualLP (standardLP A b c)) =
      LinearOptimization.dualFeasibleStd A c := by
  ext p
  constructor
  · rintro ⟨hrow, _⟩ i
    have hi := hrow i
    change -c i ≤ (-Aᵀ i) ⬝ᵥ p at hi
    rw [neg_dotProduct] at hi
    exact neg_le_neg_iff.mp hi
  · intro hp
    refine ⟨?_, ?_⟩
    · intro i
      change -c i ≤ (-Aᵀ i) ⬝ᵥ p
      rw [neg_dotProduct]
      exact neg_le_neg (hp i)
    · intro j
      trivial

private lemma dual_has_extreme_of_basis {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) ℝ) (c : Fin s → ℝ)
    (B : Fin r ↪ Fin s) (hB : LinearOptimization.IsStdBasis A B)
    (hne : (LinearOptimization.dualFeasibleStd A c).Nonempty) :
    (Set.extremePoints ℝ (LinearOptimization.dualFeasibleStd A c)).Nonempty := by
  classical
  let D : Matrix (Fin s) (Fin r) ℝ := -Aᵀ
  let T : Finset (Fin s) := Finset.univ.image B
  have hcard : T.card = r := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ B.injective]
    simp
  have hex : ∀ t : T, ∃ i, B i = t.1 := by
    intro t
    have ht := t.property
    change t.1 ∈ Finset.univ.image B at ht
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp ht
    exact ⟨i, hi⟩
  let q : T → Fin r := fun t ↦ Classical.choose (hex t)
  have hq : ∀ t : T, B (q t) = t.1 := by
    intro t
    exact Classical.choose_spec (hex t)
  have hqinj : Function.Injective q := by
    intro x y hxy
    apply Subtype.ext
    rw [← hq x, ← hq y, hxy]
  have hrowsA : LinearIndependent ℝ (fun t : T ↦ Aᵀ t.1) := by
    have hcomp := hB.comp q hqinj
    convert hcomp using 1
    funext t
    simp only [Function.comp_apply]
    rw [hq]
  have hrowsD : LinearIndependent ℝ (fun t : T ↦ D t.1) := by
    convert hrowsA.neg using 1
  have hneD : (LinearOptimization.polyhedron D (-c)).Nonempty := by
    rw [← dualFeasible_eq_polyhedron A c]
    exact hne
  have hextD :=
    (LinearOptimization.polyhedron_extreme_point_existence D (-c) hneD).out 2 0
  have : (Set.extremePoints ℝ (LinearOptimization.polyhedron D (-c))).Nonempty :=
    hextD.mp ⟨T, hcard, hrowsD⟩
  rwa [← dualFeasible_eq_polyhedron A c] at this

private lemma dual_extreme_gives_basis {r s : ℕ}
    (A : Matrix (Fin r) (Fin s) ℝ) (c : Fin s → ℝ)
    (p : Fin r → ℝ)
    (hne : (LinearOptimization.dualFeasibleStd A c).Nonempty)
    (hp : p ∈ Set.extremePoints ℝ (LinearOptimization.dualFeasibleStd A c)) :
    ∃ B : Fin r ↪ Fin s, LinearOptimization.IsStdBasis A B ∧
      (LinearOptimization.basisMatrix A B)ᵀ.mulVec p = (fun i ↦ c (B i)) := by
  classical
  let D : Matrix (Fin s) (Fin r) ℝ := -Aᵀ
  let d : Fin s → ℝ := -c
  let C := LinearOptimization.generalFormSystem D d
  have hDP : LinearOptimization.dualFeasibleStd A c =
      LinearOptimization.polyhedron D d := dualFeasible_eq_polyhedron A c
  have hCP : LinearOptimization.constraintSet C =
      LinearOptimization.polyhedron D d := constraintSet_general_eq D d
  have hneC : (LinearOptimization.constraintSet C).Nonempty := by
    rw [hCP, ← hDP]
    exact hne
  have hpmemC : p ∈ LinearOptimization.constraintSet C := by
    rw [hCP, ← hDP]
    exact hp.1
  have hpextC : p ∈ Set.extremePoints ℝ
      (LinearOptimization.constraintSet C) := by
    rw [hCP, ← hDP]
    exact hp
  have htfae := LinearOptimization.lp_vertex_extreme_bfs_equiv C p hneC hpmemC
  have hbfs : LinearOptimization.IsBasicFeasibleSolution C p :=
    (htfae.out 1 2).mp hpextC
  obtain ⟨_, T, hcard, hactive, hLI⟩ := hbfs.1
  let e : Fin r ≃ T := Fintype.equivOfCardEq (by simpa using hcard.symm)
  let B : Fin r ↪ Fin s :=
    ⟨fun i ↦ (e i).1, fun i j hij ↦ e.injective (Subtype.ext hij)⟩
  have hLID : LinearIndependent ℝ (fun t : T ↦ D t.1) := by
    simpa [C, LinearOptimization.generalFormSystem] using hLI
  have hLIDB : LinearIndependent ℝ (fun i : Fin r ↦ D (B i)) := by
    simpa [B] using hLID.comp e e.injective
  have hB : LinearOptimization.IsStdBasis A B := by
    have hneg := hLIDB.neg
    have heq : -(fun i : Fin r ↦ D (B i)) = (fun i ↦ Aᵀ (B i)) := by
      funext i j
      simp [D]
    rw [heq] at hneg
    exact hneg
  refine ⟨B, hB, ?_⟩
  funext i
  have hi := hactive (e i) (e i).property
  change D (B i) ⬝ᵥ p = d (B i) at hi
  have hi' : Aᵀ (B i) ⬝ᵥ p = c (B i) := by
    dsimp [D, d] at hi
    have hrow : (-Aᵀ) (B i) = -(Aᵀ (B i)) := by rfl
    rw [hrow] at hi
    rw [neg_dotProduct] at hi
    exact neg_inj.mp hi
  simpa [LinearOptimization.basisMatrix, Matrix.mulVec] using hi'

/-- Bertsimas--Tsitsiklis, Theorem 7.5, p. 289, combined with the
fundamental theorem of linear programming for primal and dual polyhedra. -/
theorem solution {n m : ℕ}
    (arcs : Fin m → Fin (n + 1) × Fin (n + 1)) (bsupply : Fin (n + 1) → ℝ)
    (cost : Fin m → ℝ)
    (hloop : LinearOptimization.HasNoSelfLoops arcs)
    (hconn : LinearOptimization.IsConnectedNetwork arcs)
    (hsum : ∑ i, bsupply i = 0)
    (hfin :
      LinearOptimization.lpValue cost
          (LinearOptimization.stdPolyhedron
            (LinearOptimization.truncatedIncidence arcs)
            (LinearOptimization.truncatedSupply bsupply)) ≠ ⊤ ∧
      LinearOptimization.lpValue cost
          (LinearOptimization.stdPolyhedron
            (LinearOptimization.truncatedIncidence arcs)
            (LinearOptimization.truncatedSupply bsupply)) ≠ ⊥) :
    ((∀ i, ∃ z : ℤ, bsupply i = (z : ℝ)) →
      ∃ f, LinearOptimization.IsLpOptimal cost
          (LinearOptimization.stdPolyhedron
            (LinearOptimization.truncatedIncidence arcs)
            (LinearOptimization.truncatedSupply bsupply)) f ∧
        ∀ k, ∃ z : ℤ, f k = (z : ℝ)) ∧
    ((∀ k, ∃ z : ℤ, cost k = (z : ℝ)) →
      ∃ p, LinearOptimization.IsLpDualOptimal
          (LinearOptimization.truncatedSupply bsupply)
          (LinearOptimization.dualFeasibleStd
            (LinearOptimization.truncatedIncidence arcs) cost) p ∧
        ∀ i, ∃ z : ℤ, p i = (z : ℝ)) := by
  classical
  let A := LinearOptimization.truncatedIncidence arcs
  let b := LinearOptimization.truncatedSupply bsupply
  have hroot := LinearOptimization.network_flow_integrality
    arcs bsupply cost hloop hconn hsum
  obtain ⟨f, hfopt, hfbasic⟩ := finite_std_lp_has_optimal_basic A b cost hfin
  have hA : LinearIndependent ℝ (fun i ↦ A i) :=
    LinearOptimization.network_incidence_rank arcs hloop hconn
  obtain ⟨_, B₀, hB₀, _⟩ :=
    (LinearOptimization.lp_standard_form_basic_iff A b hA f).mp hfbasic
  refine ⟨?_, ?_⟩
  · intro hbs
    refine ⟨f, hfopt, ?_⟩
    exact hroot.2.1 hbs f hfbasic
  · intro hcost
    let P := standardLP A b cost
    have hPF : LinearOptimization.generalFeasibleSet P =
        LinearOptimization.stdPolyhedron A b := standardLP_feasible A b cost
    have hPD : LinearOptimization.generalFeasibleSet
        (LinearOptimization.dualLP P) =
        LinearOptimization.dualFeasibleStd A cost :=
      standardLP_dual_feasible A b cost
    have hfoptP : LinearOptimization.IsLpOptimal P.c
        (LinearOptimization.generalFeasibleSet P) f := by
      change LinearOptimization.IsLpOptimal cost
        (LinearOptimization.generalFeasibleSet P) f
      rw [hPF]
      exact hfopt
    obtain ⟨p₀, hp₀, _⟩ := LinearOptimization.lp_strong_duality P f hfoptP
    have hp₀dual : LinearOptimization.IsLpDualOptimal b
        (LinearOptimization.dualFeasibleStd A cost) p₀ := by
      change LinearOptimization.IsLpDualOptimal b
        (LinearOptimization.generalFeasibleSet (LinearOptimization.dualLP P)) p₀ at hp₀
      rwa [hPD] at hp₀
    have hneDual : (LinearOptimization.dualFeasibleStd A cost).Nonempty :=
      ⟨p₀, hp₀dual.1⟩
    have hextDual := dual_has_extreme_of_basis A cost B₀ hB₀ hneDual
    let D : Matrix (Fin m) (Fin n) ℝ := -Aᵀ
    let d : Fin m → ℝ := -cost
    have hDP : LinearOptimization.dualFeasibleStd A cost =
        LinearOptimization.polyhedron D d := dualFeasible_eq_polyhedron A cost
    have hextD : (Set.extremePoints ℝ
        (LinearOptimization.polyhedron D d)).Nonempty := by
      rwa [← hDP]
    have hp₀optD : LinearOptimization.IsLpOptimal (-b)
        (LinearOptimization.polyhedron D d) p₀ := by
      constructor
      · rw [← hDP]
        exact hp₀dual.1
      · intro q hq
        have hq' : q ∈ LinearOptimization.dualFeasibleStd A cost := by
          rwa [hDP]
        have hle := hp₀dual.2 q hq'
        simpa [neg_dotProduct, dotProduct_comm] using neg_le_neg hle
    obtain ⟨p, hpextD, hpoptD⟩ :=
      LinearOptimization.lp_optimal_extreme_point D d (-b) hextD ⟨p₀, hp₀optD⟩
    have hpext : p ∈ Set.extremePoints ℝ
        (LinearOptimization.dualFeasibleStd A cost) := by
      rwa [hDP]
    have hpdual : LinearOptimization.IsLpDualOptimal b
        (LinearOptimization.dualFeasibleStd A cost) p := by
      constructor
      · rw [hDP]
        exact hpoptD.1
      · intro q hq
        have hqD : q ∈ LinearOptimization.polyhedron D d := by rwa [← hDP]
        have hle := hpoptD.2 q hqD
        simpa [neg_dotProduct, dotProduct_comm] using neg_le_neg hle
    obtain ⟨B, hB, hpB⟩ := dual_extreme_gives_basis A cost p hneDual hpext
    refine ⟨p, hpdual, ?_⟩
    exact hroot.2.2 hcost B hB p hpB
