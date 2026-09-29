-- Prove2me | solution 1 for MarkovMixing.dist_le_distPairs
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T03:53:22.871427+00:00
-- url     : https://prove2.me/submissions/a1ef970c-3817-4710-a915-b9caa44d874e

import Definitions.Def_mm_mixing
import Mathlib.Tactic.Linarith

open scoped BigOperators
open scoped Matrix
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (π : V → ℝ) (hπ : IsStationary P π) (t : ℕ) :
    distStationary P π t ≤ distPairs P t ∧
    distPairs P t ≤ 2 * distStationary P π t := by
  classical
  -- generic facts about the total variation supremum
  have hbdd : ∀ μ ν : V → ℝ,
      BddAbove (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|) :=
    fun μ ν => Set.Finite.bddAbove
      (Set.range fun A : Finset V => |∑ x ∈ A, μ x - ∑ x ∈ A, ν x|).toFinite
  have htv_ge : ∀ (μ ν : V → ℝ) (A : Finset V),
      |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| ≤ tvDist μ ν :=
    fun μ ν A => le_ciSup (hbdd μ ν) A
  have htv_le : ∀ (μ ν : V → ℝ) (c : ℝ),
      (∀ A : Finset V, |∑ x ∈ A, μ x - ∑ x ∈ A, ν x| ≤ c) → tvDist μ ν ≤ c :=
    fun μ ν c h => ciSup_le h
  have htv_nonneg : ∀ μ ν : V → ℝ, 0 ≤ tvDist μ ν := by
    intro μ ν
    have h := htv_ge μ ν ∅
    simpa using h
  -- the two suprema are bounded above
  have hbdd_d : BddAbove (Set.range fun x : V => tvDist (rowDist P t x) π) :=
    Set.Finite.bddAbove (Set.range fun x : V => tvDist (rowDist P t x) π).toFinite
  have hbdd_dbar :
      BddAbove (Set.range fun p : V × V => tvDist (rowDist P t p.1) (rowDist P t p.2)) :=
    Set.Finite.bddAbove
      (Set.range fun p : V × V => tvDist (rowDist P t p.1) (rowDist P t p.2)).toFinite
  have hd_ge : ∀ x : V, tvDist (rowDist P t x) π ≤ distStationary P π t :=
    fun x => le_ciSup hbdd_d x
  have hdbar_ge : ∀ x y : V,
      tvDist (rowDist P t x) (rowDist P t y) ≤ distPairs P t :=
    fun x y => le_ciSup hbdd_dbar (x, y)
  -- π is stationary for every power of P
  have hstat_pow_all : ∀ n : ℕ, π ᵥ* (P ^ n) = π := by
    intro n
    induction n with
    | zero => simp
    | succ m ih => rw [pow_succ, ← Matrix.vecMul_vecMul, ih, hπ.2]
  have hstat_pow : π ᵥ* (P ^ t) = π := hstat_pow_all t
  have hπA : ∀ A : Finset V, ∑ y ∈ A, π y = ∑ w, π w * ∑ y ∈ A, (rowDist P t w) y := by
    intro A
    have hy : ∀ y : V, π y = ∑ w, π w * (P ^ t) w y := fun y => (congrFun hstat_pow y).symm
    rw [Finset.sum_congr rfl fun y _ => hy y, Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => by rw [← Finset.mul_sum]; rfl
  constructor
  · -- d(t) ≤ d̄(t) by averaging over the stationary distribution
    refine ciSup_le fun x => htv_le _ _ _ fun A => ?_
    have hsplit : ∑ y ∈ A, (rowDist P t x) y - ∑ y ∈ A, π y
        = ∑ w, π w * (∑ y ∈ A, (rowDist P t x) y - ∑ y ∈ A, (rowDist P t w) y) := by
      rw [Finset.sum_congr rfl fun w _ => mul_sub (π w) _ _, Finset.sum_sub_distrib,
        ← Finset.sum_mul, hπ.1.2, one_mul, ← hπA A]
    rw [hsplit]
    calc |∑ w, π w * (∑ y ∈ A, (rowDist P t x) y - ∑ y ∈ A, (rowDist P t w) y)|
        ≤ ∑ w, |π w * (∑ y ∈ A, (rowDist P t x) y - ∑ y ∈ A, (rowDist P t w) y)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ w, π w * distPairs P t := by
          refine Finset.sum_le_sum fun w _ => ?_
          rw [abs_mul, abs_of_nonneg (hπ.1.1 w)]
          exact mul_le_mul_of_nonneg_left
            (le_trans (htv_ge _ _ A) (hdbar_ge x w)) (hπ.1.1 w)
      _ = distPairs P t := by rw [← Finset.sum_mul, hπ.1.2, one_mul]
  · -- d̄(t) ≤ 2 d(t) by the triangle inequality through π
    refine ciSup_le fun p => htv_le _ _ _ fun A => ?_
    have htri : |∑ y ∈ A, (rowDist P t p.1) y - ∑ y ∈ A, (rowDist P t p.2) y|
        ≤ |∑ y ∈ A, (rowDist P t p.1) y - ∑ y ∈ A, π y|
          + |∑ y ∈ A, π y - ∑ y ∈ A, (rowDist P t p.2) y| := by
      have := abs_sub_abs_le_abs_sub
        (∑ y ∈ A, (rowDist P t p.1) y - ∑ y ∈ A, π y)
        (∑ y ∈ A, (rowDist P t p.2) y - ∑ y ∈ A, π y)
      have h2 : ∑ y ∈ A, (rowDist P t p.1) y - ∑ y ∈ A, (rowDist P t p.2) y
          = (∑ y ∈ A, (rowDist P t p.1) y - ∑ y ∈ A, π y)
            - (∑ y ∈ A, (rowDist P t p.2) y - ∑ y ∈ A, π y) := by ring
      rw [h2]
      refine le_trans (abs_sub _ _) ?_
      have h3 : |∑ y ∈ A, (rowDist P t p.2) y - ∑ y ∈ A, π y|
          = |∑ y ∈ A, π y - ∑ y ∈ A, (rowDist P t p.2) y| := abs_sub_comm _ _
      rw [h3]
    have h1 : |∑ y ∈ A, (rowDist P t p.1) y - ∑ y ∈ A, π y| ≤ distStationary P π t :=
      le_trans (htv_ge _ _ A) (hd_ge p.1)
    have h2 : |∑ y ∈ A, π y - ∑ y ∈ A, (rowDist P t p.2) y| ≤ distStationary P π t := by
      rw [abs_sub_comm]
      exact le_trans (htv_ge _ _ A) (hd_ge p.2)
    linarith
