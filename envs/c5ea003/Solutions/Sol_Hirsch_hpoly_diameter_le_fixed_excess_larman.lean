-- Prove2me | solution 1 for Hirsch.hpoly_diameter_le_fixed_excess_larman
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-12T17:29:12.606458+00:00
-- url     : https://prove2.me/submissions/cd24addc-446f-4d16-b814-85315057c98f

import Theorems.Thm_Hirsch_larman_bound
import Theorems.Thm_Hirsch_facet_reduction
import Mathlib
import Definitions.Def_Hirsch_model
open scoped RealInnerProductSpace
open Set Hirsch


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

#print axioms vertex_tight_rows_span_checked

end HirschPolynomialAccess

/-!
# Direct small-excess descent

The two geometric library inputs are explicit propositions, not axioms or
imported theorem stubs. They match the live Prove2Me statements of
`Hirsch.dimension_three_bound` and `Hirsch.facet_reduction`.

A separate platform solution supplies those already-Proved inputs. This driver
also exposes the nonzero-row counting needed when tautologies are present.
-/

open Set Hirsch
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section
namespace HirschLowExcess

noncomputable def tightNonzeroRows {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, x⟫ = b i)

/-- A vertex has at least d distinct tight nonzero describing rows. -/
theorem dimension_le_tightNonzeroRows_card {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    d ≤ (tightNonzeroRows a b x).card := by
  classical
  let S := tightNonzeroRows a b x
  let T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun y i => ⟪a i.1, y⟫
      map_add' := by
        intro y z
        funext i
        simp [inner_add_right]
      map_smul' := by
        intro r y
        funext i
        simp [inner_smul_right] }
  have hT : Function.Injective T := by
    intro y z hyz
    apply sub_eq_zero.mp
    apply HirschPolynomialAccess.vertex_tight_rows_span_checked d n a b x hx (y - z)
    intro i hi
    by_cases hai : a i = 0
    · simp [hai]
    · have hiS : i ∈ S := by simp [S, tightNonzeroRows, hai, hi]
      have hrow := congrFun hyz ⟨i, hiS⟩
      change ⟪a i, y⟫ = ⟪a i, z⟫ at hrow
      rw [inner_sub_right, hrow, sub_self]
  have hdim := LinearMap.finrank_le_finrank_of_injective hT
  simpa [S] using hdim

/-- The shared tight row can be chosen nonzero even with zero tautologies. -/
theorem vertices_share_nonzero_tight_row_of_n_lt_two_d {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) (hn : n < 2 * d) :
    ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ = b i := by
  classical
  let U := tightNonzeroRows a b u
  let V := tightNonzeroRows a b v
  have huCard : d ≤ U.card := dimension_le_tightNonzeroRows_card a b u hu
  have hvCard : d ≤ V.card := dimension_le_tightNonzeroRows_card a b v hv
  by_contra hnone
  have hdis : Disjoint U V := by
    apply Finset.disjoint_left.mpr
    intro i hiU hiV
    have hU : a i ≠ 0 ∧ ⟪a i, u⟫ = b i := by
      simpa [U, tightNonzeroRows] using hiU
    have hV : a i ≠ 0 ∧ ⟪a i, v⟫ = b i := by
      simpa [V, tightNonzeroRows] using hiV
    exact hnone ⟨i, hU.1, hU.2, hV.2⟩
  have hsum := Finset.card_union_of_disjoint hdis
  have hbound : (U ∪ V).card ≤ n := by
    calc
      (U ∪ V).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = n := by simp
  omega

/-- Exact type of the already-Proved low-dimensional Hirsch input. -/
def LowDimensionalHirsch : Prop :=
  ∀ (d n : ℕ), d ≤ 3 →
    ∀ (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (n - d)

/-- Exact type of the already-Proved equality-section/facet reduction input.
Only ambient edge routing is requested, matching the public theorem. -/
def FacetWalkReduction : Prop :=
  ∀ (d k : ℕ) (a : Fin (k + 1) → EuclideanSpace ℝ (Fin d))
    (b : Fin (k + 1) → ℝ) (i : Fin (k + 1)), a i ≠ 0 →
    Bornology.IsBounded (Hpoly a b) → ∀ B : ℕ,
    (∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d - 1))) (b' : Fin k → ℝ),
      Bornology.IsBounded (Hpoly a' b') → DiamLE (Hpoly a' b') B) →
    ∀ (u v : EuclideanSpace ℝ (Fin d)),
      u ∈ extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} →
      v ∈ extremePoints ℝ {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} →
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d), w 0 = u ∧ w B = v ∧
        ∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1))


end HirschLowExcess
end
namespace HirschProduct
lemma pad_walk {E : Type*} (R : E → E → Prop)
    {u v : E} {A B : ℕ} (hAB : A ≤ B)
    (w : ℕ → E) (h0 : w 0 = u) (hA : w A = v)
    (hs : ∀ j < A, w j = w (j + 1) ∨ R (w j) (w (j + 1))) :
    ∃ w' : ℕ → E, w' 0 = u ∧ w' B = v ∧
      ∀ j < B, w' j = w' (j + 1) ∨ R (w' j) (w' (j + 1)) := by
  let w' : ℕ → E := fun j => w (min j A)
  refine ⟨w', ?_, ?_, ?_⟩
  · simpa only [w', Nat.zero_min] using h0
  · simpa only [w', Nat.min_eq_right hAB] using hA
  · intro j hj
    by_cases hjA : j < A
    · have h0 : j ≤ A := by omega
      have h1 : j + 1 ≤ A := by omega
      simpa only [w', Nat.min_eq_left h0, Nat.min_eq_left h1] using hs j hjA
    · have h0 : A ≤ j := by omega
      have h1 : A ≤ j + 1 := by omega
      exact Or.inl (by simp only [w', Nat.min_eq_right h0, Nat.min_eq_right h1])

end HirschProduct
namespace HirschCircuitLocalization
def LarmanHpolyBound : Prop :=
  ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
    (Hpoly a b).Nonempty → Bornology.IsBounded (Hpoly a b) →
    DiamLE (Hpoly a b) (n * 2 ^ (d - 3))


end HirschCircuitLocalization

/-! Classical equality-section descent with a Larman base at fixed row excess.
The inputs are the already-Proved facet reduction and Larman propositions.
This bound is exponential in excess, not a uniform polynomial Hirsch bound. -/
open Set Hirsch HirschPolynomialAccess
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace HirschLowExcess
open HirschCircuitLocalization

def excessLarmanBudget (E : ℕ) : ℕ := 2 * E * 2 ^ (E - 3)

/-- When `n<=d+E`, descend through a shared nonzero tight row until `d<=E`.
Then at most `2E` inequalities remain, so Larman costs at most this fixed
function of E. The descent adds neither access steps nor a multiplicative cost. -/
theorem hpoly_diamLE_fixed_excess_larman
    (hlar : LarmanHpolyBound) (hfacet : FacetWalkReduction) (E : ℕ) :
    ∀ (d n : ℕ) (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ),
      n ≤ d + E → Bornology.IsBounded (Hpoly a b) →
      DiamLE (Hpoly a b) (excessLarmanBudget E) := by
  intro d
  induction d using Nat.strong_induction_on with
  | h d ih =>
    intro n a b hrows hbd
    by_cases hd : d ≤ E
    · by_cases hne : (Hpoly a b).Nonempty
      · have hbound := hlar d n a b hne hbd
        have hcost : n * 2 ^ (d-3) ≤ excessLarmanBudget E := by
          apply Nat.mul_le_mul (show n ≤ 2*E by omega)
          exact Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)
        intro u hu v hv
        obtain ⟨w, hw0, hwB, hs⟩ := hbound u hu v hv
        exact HirschProduct.pad_walk _ hcost w hw0 hwB hs
      · intro u hu
        exact False.elim (hne ⟨u, hu.1⟩)
    · intro u hu v hv
      have hsub : n < 2*d := by omega
      obtain ⟨i, hai, hui, hvi⟩ :=
        vertices_share_nonzero_tight_row_of_n_lt_two_d a b u v hu hv hsub
      cases n with
      | zero => exact Fin.elim0 i
      | succ k =>
        have hlow : ∀ (a' : Fin k → EuclideanSpace ℝ (Fin (d-1))) (b' : Fin k → ℝ),
            Bornology.IsBounded (Hpoly a' b') →
            DiamLE (Hpoly a' b') (excessLarmanBudget E) := by
          intro a' b' hbd'
          exact ih (d-1) (by omega) k a' b' (by omega) hbd'
        have huF : u ∈ extremePoints ℝ
            {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} := by
          refine ⟨⟨hu.1, hui⟩, ?_⟩
          intro x hx y hy hseg
          exact hu.2 hx.1 hy.1 hseg
        have hvF : v ∈ extremePoints ℝ
            {x | x ∈ Hpoly a b ∧ ⟪a i, x⟫ = b i} := by
          refine ⟨⟨hv.1, hvi⟩, ?_⟩
          intro x hx y hy hseg
          exact hv.2 hx.1 hy.1 hseg
        exact hfacet d k a b i hai hbd (excessLarmanBudget E) hlow u v huF hvF

#print axioms hpoly_diamLE_fixed_excess_larman
end HirschLowExcess
end

theorem solution
    (E d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hrows : n ≤ d + E) (hbd : Bornology.IsBounded (Hpoly a b)) :
    DiamLE (Hpoly a b) (2 * E * 2 ^ (E - 3)) := by
  exact HirschLowExcess.hpoly_diamLE_fixed_excess_larman
    Hirsch.larman_bound Hirsch.facet_reduction E d n a b hrows hbd
