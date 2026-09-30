-- Prove2me | solution 1 for Hirsch.vertex_has_injective_target_tight_basis
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T23:06:38.368704+00:00
-- url     : https://prove2.me/submissions/63c8d2b9-2c24-4c59-9c3a-6769a095f63e

import Mathlib
import Definitions.Def_Hirsch_model
open Set Hirsch
open scoped BigOperators RealInnerProductSpace

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000

namespace HirschPolynomialAccess

/-- A direct finite-perturbation proof, with no imported theorem stubs.
A direction annihilating all inequalities active at a vertex must be zero. -/
theorem vertex_tight_rows_span_checked
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (y : EuclideanSpace ℝ (Fin d))
    (horth : ∀ i, ⟪a i, x⟫ = b i → ⟪a i, y⟫ = 0) :
    y = 0 := by
  classical
  have hlocal : ∀ i : Fin n, ∃ t : ℝ,
      0 < t ∧ t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    by_cases hi : ⟪a i, x⟫ = b i
    · refine ⟨1, zero_lt_one, ?_⟩
      rw [horth i hi, abs_zero, mul_zero, hi, sub_self]
    · have hs : 0 < b i - ⟪a i, x⟫ := sub_pos.mpr (lt_of_le_of_ne (hx.1 i) hi)
      have hd : 0 < |⟪a i, y⟫| + 1 := by positivity
      let t : ℝ := (b i - ⟪a i, x⟫) / (|⟪a i, y⟫| + 1)
      have ht : 0 < t := div_pos hs hd
      have hprod : t * (|⟪a i, y⟫| + 1) = b i - ⟪a i, x⟫ := by
        dsimp [t]
        exact div_mul_cancel₀ _ (ne_of_gt hd)
      exact ⟨t, ht, by nlinarith⟩
  choose e hepos hebound using hlocal
  have huniform : ∀ S : Finset (Fin n), ∃ t : ℝ,
      0 < t ∧ ∀ i ∈ S, t ≤ e i := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨1, zero_lt_one, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨t, ht, hti⟩ := ih
      refine ⟨min (e i) t, lt_min (hepos i) ht, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjS
      · subst j
        exact min_le_left _ _
      · exact (min_le_right _ _).trans (hti j hjS)
  obtain ⟨t, ht, hte⟩ := huniform Finset.univ
  have hbudget : ∀ i, t * |⟪a i, y⟫| ≤ b i - ⟪a i, x⟫ := by
    intro i
    exact (mul_le_mul_of_nonneg_right (hte i (Finset.mem_univ i))
      (abs_nonneg _)).trans (hebound i)
  have hp : x + t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (le_abs_self ⟪a i, y⟫) ht.le
    rw [inner_add_right, inner_smul_right]
    linarith [hbudget i]
  have hm : x - t • y ∈ Hpoly a b := by
    intro i
    have hmul := mul_le_mul_of_nonneg_left (neg_le_abs ⟪a i, y⟫) ht.le
    rw [mul_neg] at hmul
    rw [inner_sub_right, inner_smul_right]
    linarith [hbudget i]
  have hmid : x ∈ openSegment ℝ (x + t • y) (x - t • y) := by
    refine ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num,
      by norm_num, ?_⟩
    module
  have hpeq : x + t • y = x := hx.2 hp hm hmid
  have hty : t • y = 0 := by
    have h := congrArg (fun z => z - x) hpeq
    simpa using h
  exact (smul_eq_zero.mp hty).resolve_left (ne_of_gt ht)


end HirschPolynomialAccess

/-! Extract the target-tight basis required by the all-row mass construction.
No simplicity, row independence, or supplied basis is assumed at the target. -/
open Set Hirsch HirschPolynomialAccess
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section
namespace HirschTargetDeletion

/-- The existing vertex annihilator theorem implies that all tight normals span. -/
theorem target_tight_normals_span_top {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    Submodule.span ℝ (a '' {i | ⟪a i, v⟫ = b i}) = ⊤ := by
  apply Submodule.orthogonal_eq_bot_iff.mp
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  apply vertex_tight_rows_span_checked d n a b v hv z
  intro i hi
  have hai : a i ∈ Submodule.span ℝ (a '' {j | ⟪a j, v⟫ = b j}) :=
    Submodule.subset_span ⟨i, hi, rfl⟩
  exact Submodule.inner_right_of_mem_orthogonal hai hz

/-- Select exactly d distinct original tight rows, with injective row evaluation.
This includes nonsimple targets with more than d tight rows. -/
theorem exists_target_tight_basis {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ e : Fin d ↪ Fin n,
      Function.Injective ((fun x : EuclideanSpace ℝ (Fin d) => fun k : Fin d => ⟪a (e k), x⟫)) ∧
      ∀ k, ⟪a (e k), v⟫ = b (e k) := by
  classical
  let T := {i : Fin n | ⟪a i, v⟫ = b i}
  let normals : T → EuclideanSpace ℝ (Fin d) := fun i => a i.1
  have htop : Submodule.span ℝ (Set.range normals) = ⊤ := by
    have he : Set.range normals = a '' T := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i.1, i.2, rfl⟩
      · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, hi⟩, rfl⟩
    rw [he]
    exact target_tight_normals_span_top a b v hv
  obtain ⟨κ, f, hf, hspan, hli⟩ := exists_linearIndependent' ℝ normals
  letI : Fintype κ := Fintype.ofInjective f hf
  let B := Module.Basis.mk hli (by rw [hspan, htop])
  have hcard : Fintype.card κ = d := by
    rw [← Module.finrank_eq_card_basis B]
    exact finrank_euclideanSpace_fin (𝕜 := ℝ)
  let q : Fin d ≃ κ := Fintype.equivOfCardEq (by simp [hcard])
  let e : Fin d ↪ Fin n :=
    ⟨fun k => (f (q k)).1, Subtype.val_injective.comp (hf.comp q.injective)⟩
  refine ⟨e, ?_, fun k => (f (q k)).2⟩
  intro x y hxy
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℝ)).mp
  have horth : ∀ k : κ, ⟪B k, x-y⟫ = 0 := by
    intro k
    have h := congrFun hxy (q.symm k)
    change ⟪a (e (q.symm k)), x⟫ = ⟪a (e (q.symm k)), y⟫ at h
    have he : a (e (q.symm k)) = B k := by simp [e, B, normals]
    rw [he] at h
    simp [inner_sub_right, h]
  calc
    ⟪x-y, x-y⟫ = ⟪∑ k, B.repr (x-y) k • B k, x-y⟫ := by rw [B.sum_repr]
    _ = 0 := by simp [sum_inner, inner_smul_left, horth]


end HirschTargetDeletion
end

theorem solution {d n : ℕ} (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (v : EuclideanSpace ℝ (Fin d)) (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    ∃ e : Fin d ↪ Fin n,
      Function.Injective (fun x : EuclideanSpace ℝ (Fin d) => fun k : Fin d => ⟪a (e k), x⟫) ∧
      ∀ k, ⟪a (e k), v⟫ = b (e k) := by
  exact HirschTargetDeletion.exists_target_tight_basis a b v hv
