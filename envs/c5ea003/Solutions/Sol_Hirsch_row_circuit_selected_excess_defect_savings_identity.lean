-- Prove2me | solution 1 for Hirsch.row_circuit_selected_excess_defect_savings_identity
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-11T19:45:51.054204+00:00
-- url     : https://prove2.me/submissions/8a675045-8a44-49ae-8b6a-5389fd003a5e

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_circuit_model
import Definitions.Def_Hirsch_circuit_slack_model
import Definitions.Def_Hirsch_common_face_geometry
open scoped BigOperators RealInnerProductSpace InnerProduct
open Set Module Hirsch

set_option autoImplicit false

-- BEGIN Solutions.PolynomialVertexSpan
section

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
end

-- BEGIN Solutions.PolynomialSeparatedRows
section

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 2000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- An extreme point in ambient dimension `d` has at least `d` distinct
nonzero tight rows in any finite H-description. Zero normal rows do not
contribute to the spanning condition. -/
lemma nonzero_tight_rows_card_ge_dim
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    d ≤ (Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, x⟫ = b i)).card := by
  classical
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, x⟫ = b i)
  by_contra hcard
  have hlt : S.card < d := by
    simpa [S] using (Nat.lt_of_not_ge hcard)
  let T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (S → ℝ) :=
    { toFun := fun y i => ⟪a i.1, y⟫
      map_add' := by
        intro y z
        funext i
        simp [inner_add_right]
      map_smul' := by
        intro c y
        funext i
        simp [inner_smul_right] }
  have hnotinj : ¬ Function.Injective T := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    have hcod : Module.finrank ℝ (S → ℝ) = S.card := by
      simp [Fintype.card_coe]
    rw [hdom, hcod] at hle
    omega
  have hker : T.ker ≠ ⊥ := by
    intro hk
    apply hnotinj
    rw [← LinearMap.ker_eq_bot]
    exact hk
  obtain ⟨y, hyker, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hyorth : ∀ j, ⟪a j, x⟫ = b j → ⟪a j, y⟫ = 0 := by
    intro j hj
    by_cases haj : a j = 0
    · simp [haj]
    · have hjS : j ∈ S := by
        simp [S, haj, hj]
      have hTy : T y = 0 := LinearMap.mem_ker.1 hyker
      have hcoord := congrFun hTy ⟨j, hjS⟩
      change ⟪a j, y⟫ = 0 at hcoord
      exact hcoord
  have hyz := vertex_tight_rows_span_checked d n a b x hx y hyorth
  exact hy0 hyz

/-- Separated extreme vertices require at least `2d` describing rows. -/
lemma separated_extremes_n_ge_two_d
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ j, a j ≠ 0 →
      ⟪a j, u⟫ ≠ b j ∨ ⟪a j, v⟫ ≠ b j) :
    2 * d ≤ n := by
  classical
  let SU : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, u⟫ = b i)
  let SV : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, v⟫ = b i)
  have hU : d ≤ SU.card := by
    simpa [SU] using nonzero_tight_rows_card_ge_dim a b u hu
  have hV : d ≤ SV.card := by
    simpa [SV] using nonzero_tight_rows_card_ge_dim a b v hv
  have hdisj : Disjoint SU SV := by
    refine Finset.disjoint_left.2 ?_
    intro j hju hjv
    have huj := (Finset.mem_filter.1 hju).2
    have hvj := (Finset.mem_filter.1 hjv).2
    rcases hsep j huj.1 with hnotu | hnotv
    · exact hnotu huj.2
    · exact hnotv hvj.2
  have hsum : SU.card + SV.card = (SU ∪ SV).card := by
    simpa using (Finset.card_union_of_disjoint hdisj).symm
  have hunion : (SU ∪ SV).card ≤ n := by
    have hsub : SU ∪ SV ⊆ (Finset.univ : Finset (Fin n)) := by simp
    calc
      (SU ∪ SV).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card hsub
      _ = n := by simp
  omega

end HirschPolynomialAccess
end
end

-- BEGIN Solutions.PolynomialExcessFaceRank
section

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 3000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

noncomputable def commonSourceRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, u⟫ = b i ∧ ⟪a i, x⟫ = b i)

noncomputable def neutralRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, u⟫ ≠ b i ∧ ⟪a i, v⟫ ≠ b i)

noncomputable def rowEvalMap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (S : Finset (Fin n)) :
    EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (S → ℝ) :=
  { toFun := fun y i => ⟪a i.1, y⟫
    map_add' := by
      intro y z
      funext i
      simp [inner_add_right]
    map_smul' := by
      intro c y
      funext i
      simp [inner_smul_right] }

/-- Directions annihilating every nonzero row active at both `u` and `x`. -/
noncomputable def commonDirection
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
  (rowEvalMap a (commonSourceRows a b u x)).ker

/-- Neutral-row evaluation is injective on the common-source directions of
any target-avoiding vertex. Separation and extremality of `u,v` are not needed. -/
lemma neutral_eval_injective
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (havoid : ∀ i, a i ≠ 0 →
      ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) :
    Function.Injective
      ((rowEvalMap a (neutralRows a b u v)).domRestrict
        (commonDirection a b u x)) := by
  classical
  let C := commonSourceRows a b u x
  let N := neutralRows a b u v
  let W := commonDirection a b u x
  let T : W →ₗ[ℝ] (N → ℝ) := (rowEvalMap a N).domRestrict W
  change Function.Injective T
  intro y z hyz
  apply Subtype.ext
  let q : W := y - z
  have hTq : T q = 0 := by
    rw [map_sub, hyz, sub_self]
  have hqCommon : ∀ i, i ∈ C → ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
    intro i hiC
    have hker : (rowEvalMap a C) (q : EuclideanSpace ℝ (Fin d)) = 0 :=
      LinearMap.mem_ker.1 q.2
    change (rowEvalMap a C) (q : EuclideanSpace ℝ (Fin d)) ⟨i, hiC⟩ = 0
    exact congrFun hker ⟨i, hiC⟩
  have hqNeutral : ∀ i, i ∈ N → ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
    intro i hiN
    change T q ⟨i, hiN⟩ = 0
    exact congrFun hTq ⟨i, hiN⟩
  have hqTight : ∀ i, ⟪a i, x⟫ = b i →
      ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
    intro i hix
    by_cases hai : a i = 0
    · simp [hai]
    by_cases hiu : ⟪a i, u⟫ = b i
    · have hiC : i ∈ C := by
        simp [C, commonSourceRows, hai, hiu, hix]
      exact hqCommon i hiC
    · have hiv : ⟪a i, v⟫ ≠ b i := by
        intro hivEq
        exact (havoid i hai hivEq) hix
      have hiN : i ∈ N := by
        simp [N, neutralRows, hai, hiu, hiv]
      exact hqNeutral i hiN
  have hq0 := vertex_tight_rows_span_checked d n a b x hx
    (q : EuclideanSpace ℝ (Fin d)) hqTight
  change (y : EuclideanSpace ℝ (Fin d)) - (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
  exact sub_eq_zero.mp hq0

/-- Sharper than counting neutral rows: linearly dependent rows cost only
the rank of their joint evaluation map. -/
lemma common_direction_finrank_le_neutral_rank
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (havoid : ∀ i, a i ≠ 0 →
      ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) :
    Module.finrank ℝ (commonDirection a b u x) ≤
      Module.finrank ℝ (rowEvalMap a (neutralRows a b u v)).range := by
  let W := commonDirection a b u x
  let R := rowEvalMap a (neutralRows a b u v)
  let T : W →ₗ[ℝ] R.range := R.rangeRestrict.comp W.subtype
  have hTin : Function.Injective T := by
    intro y z h
    apply neutral_eval_injective a b u v x hx havoid
    exact congrArg Subtype.val h
  exact LinearMap.finrank_le_finrank_of_injective hTin

/-- The original neutral-count estimate, now deduced from an explicit injective map. -/
lemma common_direction_finrank_le_neutral_card
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (_hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (havoid : ∀ i, a i ≠ 0 →
      ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) :
    Module.finrank ℝ (commonDirection a b u x) ≤
      (neutralRows a b u v).card := by
  have hle := LinearMap.finrank_le_finrank_of_injective
    (neutral_eval_injective a b u v x hx havoid)
  simpa using hle

/-- There are at most `n - 2*d` neutral rows for separated extreme endpoints. -/
lemma neutral_card_le_excess
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    (neutralRows a b u v).card ≤ n - 2 * d := by
  classical
  let SU : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, u⟫ = b i)
  let SV : Finset (Fin n) :=
    Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, v⟫ = b i)
  let N := neutralRows a b u v
  have hU : d ≤ SU.card := by
    simpa [SU] using nonzero_tight_rows_card_ge_dim a b u hu
  have hV : d ≤ SV.card := by
    simpa [SV] using nonzero_tight_rows_card_ge_dim a b v hv
  have hUV : Disjoint SU SV := by
    refine Finset.disjoint_left.2 ?_
    intro i hiU hiV
    have hu' := (Finset.mem_filter.1 hiU).2
    have hv' := (Finset.mem_filter.1 hiV).2
    rcases hsep i hu'.1 with hnu | hnv
    · exact hnu hu'.2
    · exact hnv hv'.2
  have hUN : Disjoint SU N := by
    refine Finset.disjoint_left.2 ?_
    intro i hiU hiN
    exact (Finset.mem_filter.1 hiN).2.2.1 (Finset.mem_filter.1 hiU).2.2
  have hVN : Disjoint SV N := by
    refine Finset.disjoint_left.2 ?_
    intro i hiV hiN
    exact (Finset.mem_filter.1 hiN).2.2.2 (Finset.mem_filter.1 hiV).2.2
  have hdisj : Disjoint (SU ∪ SV) N := Finset.disjoint_union_left.2 ⟨hUN, hVN⟩
  have hcardUnion : (SU ∪ SV).card = SU.card + SV.card :=
    Finset.card_union_of_disjoint hUV
  have htotal : (SU ∪ SV ∪ N).card ≤ n := by
    have hsub : SU ∪ SV ∪ N ⊆ (Finset.univ : Finset (Fin n)) := by simp
    calc
      (SU ∪ SV ∪ N).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card hsub
      _ = n := by simp
  rw [Finset.card_union_of_disjoint hdisj, hcardUnion] at htotal
  have h2d : 2 * d ≤ n := separated_extremes_n_ge_two_d a b u v hu hv hsep
  change N.card ≤ n - 2 * d
  omega

lemma common_direction_finrank_le_excess
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (havoid : ∀ i, a i ≠ 0 →
      ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) :
    Module.finrank ℝ (commonDirection a b u x) ≤ n - 2 * d :=
  (common_direction_finrank_le_neutral_card a b u v x hx hsep havoid).trans
    (neutral_card_le_excess a b u v hu hv hsep)


end HirschPolynomialAccess
end
end

-- BEGIN Solutions.PolynomialCommonFace
section

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 2500000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

noncomputable def commonFace
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    Set (EuclideanSpace ℝ (Fin d)) :=
  {y | y ∈ Hpoly a b ∧
    ∀ i, i ∈ commonSourceRows a b u x → ⟪a i, y⟫ = b i}

lemma mem_commonFace_iff
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x y : EuclideanSpace ℝ (Fin d)) :
    y ∈ commonFace a b u x ↔
      y ∈ Hpoly a b ∧
      ∀ i, i ∈ commonSourceRows a b u x → ⟪a i, y⟫ = b i := by
  rfl

/-- The intersection of a polytope with any collection of its supporting
hyperplanes is an extreme subset (face) of the polytope. -/
lemma commonFace_isExtreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    IsExtreme ℝ (Hpoly a b) (commonFace a b u x) := by
  refine ⟨?_, ?_⟩
  · intro y hy
    exact hy.1
  · intro p hp q hq z hz hzopen
    refine ⟨hp, ?_⟩
    intro i hiC
    have hztight : ⟪a i, z⟫ = b i := hz.2 i hiC
    have hp_le := hp i
    have hq_le := hq i
    obtain ⟨α, β, hα, hβ, hαβ, hzcomb⟩ := hzopen
    have hinner : ⟪a i, z⟫ = α * ⟪a i, p⟫ + β * ⟪a i, q⟫ := by
      rw [← hzcomb]
      simp [inner_add_right, inner_smul_right]
    have hαpos : 0 < α := hα
    have hβnonneg : 0 ≤ β := hβ.le
    by_contra hptight
    have hp_lt : ⟪a i, p⟫ < b i := lt_of_le_of_ne hp_le hptight
    have h1 : α * ⟪a i, p⟫ < α * b i :=
      mul_lt_mul_of_pos_left hp_lt hαpos
    have h2 : β * ⟪a i, q⟫ ≤ β * b i :=
      mul_le_mul_of_nonneg_left hq_le hβnonneg
    have hb : α * b i + β * b i = b i := by
      rw [← add_mul, hαβ, one_mul]
    linarith

lemma commonFace_u_mem
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) :
    u ∈ commonFace a b u x := by
  refine ⟨hu, ?_⟩
  intro i hiC
  exact (Finset.mem_filter.1 hiC).2.2.1

lemma commonFace_x_mem
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ Hpoly a b) :
    x ∈ commonFace a b u x := by
  refine ⟨hx, ?_⟩
  intro i hiC
  exact (Finset.mem_filter.1 hiC).2.2.2

/-- The common face is the intersection of the original polytope with the
affine translate `u + commonDirection`. -/
lemma mem_commonFace_iff_sub_mem_commonDirection
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x y : EuclideanSpace ℝ (Fin d)) :
    y ∈ commonFace a b u x ↔
      y ∈ Hpoly a b ∧ y - u ∈ commonDirection a b u x := by
  constructor
  · intro hy
    refine ⟨hy.1, ?_⟩
    rw [commonDirection, LinearMap.mem_ker]
    funext ii
    have hiC : ii.1 ∈ commonSourceRows a b u x := ii.2
    have hyi : ⟪a ii.1, y⟫ = b ii.1 := hy.2 ii.1 hiC
    have hui : ⟪a ii.1, u⟫ = b ii.1 :=
      (Finset.mem_filter.1 hiC).2.2.1
    change ⟪a ii.1, y - u⟫ = 0
    rw [inner_sub_right, hyi, hui]
    ring
  · rintro ⟨hyP, hdir⟩
    refine ⟨hyP, ?_⟩
    intro i hiC
    have hker : rowEvalMap a (commonSourceRows a b u x) (y - u) = 0 :=
      LinearMap.mem_ker.1 hdir
    have hcoord : ⟪a i, y - u⟫ = 0 := by
      change (rowEvalMap a (commonSourceRows a b u x) (y - u)) ⟨i, hiC⟩ = 0
      exact congrFun hker ⟨i, hiC⟩
    have hui : ⟪a i, u⟫ = b i :=
      (Finset.mem_filter.1 hiC).2.2.1
    rw [inner_sub_right, hui] at hcoord
    linarith

lemma commonFace_extremePoints_subset_parent
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    extremePoints ℝ (commonFace a b u x) ⊆
      extremePoints ℝ (Hpoly a b) :=
  (commonFace_isExtreme a b u x).extremePoints_subset_extremePoints

/-- Any edge in the common face is an edge of the parent polytope. -/
lemma commonFace_adj_to_parent
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    {p q : EuclideanSpace ℝ (Fin d)}
    (hadj : Adj (commonFace a b u x) p q) :
    Adj (Hpoly a b) p q := by
  refine ⟨hadj.1, ?_⟩
  exact (commonFace_isExtreme a b u x).trans hadj.2

end HirschPolynomialAccess
end
end

-- BEGIN Solutions.PolynomialCommonFaceCoords
section

open scoped RealInnerProductSpace InnerProduct
open Set Hirsch

set_option maxHeartbeats 3000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

noncomputable def commonFaceDim
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) : ℕ :=
  Module.finrank ℝ (commonDirection a b u x)

noncomputable def commonFaceRepr
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    commonDirection a b u x ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (commonFaceDim a b u x)) := by
  simpa [commonFaceDim] using
    (stdOrthonormalBasis ℝ (commonDirection a b u x)).repr

/-- Isometric inclusion of coordinates on the common-source direction space
into the ambient Euclidean space. -/
noncomputable def commonFaceLift
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (commonFaceDim a b u x)) →ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin d) :=
  (commonDirection a b u x).subtypeₗᵢ.comp
    (commonFaceRepr a b u x).symm.toLinearIsometry

noncomputable def commonFaceLiftCLM
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (commonFaceDim a b u x)) →L[ℝ]
      EuclideanSpace ℝ (Fin d) :=
  (commonFaceLift a b u x).toContinuousLinearMap

/-- The original row normal restricted to the common-source direction space,
expressed in orthonormal Euclidean coordinates. -/
noncomputable def commonFaceA
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) (i : Fin n) :
    EuclideanSpace ℝ (Fin (commonFaceDim a b u x)) :=
  ContinuousLinearMap.adjoint (commonFaceLiftCLM a b u x) (a i)

noncomputable def commonFaceB
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) (i : Fin n) : ℝ :=
  b i - ⟪a i, u⟫

noncomputable def commonFacePoint
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    EuclideanSpace ℝ (Fin d) :=
  u + commonFaceLift a b u x q

lemma commonFace_inner_restricted
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (i : Fin n) (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    ⟪commonFaceA a b u x i, q⟫ =
      ⟪a i, commonFaceLift a b u x q⟫ := by
  have h := ContinuousLinearMap.adjoint_inner_right
    (commonFaceLiftCLM a b u x) q (a i)
  simpa [commonFaceA, commonFaceLiftCLM, real_inner_comm] using h

lemma commonFaceLift_mem_direction
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    commonFaceLift a b u x q ∈ commonDirection a b u x := by
  change (((commonFaceRepr a b u x).symm q : commonDirection a b u x) :
    EuclideanSpace ℝ (Fin d)) ∈ commonDirection a b u x
  exact ((commonFaceRepr a b u x).symm q).property

lemma commonFacePoint_sub
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    commonFacePoint a b u x q - u = commonFaceLift a b u x q := by
  simp [commonFacePoint]

/-- Exact coordinate model of the common source face. All original rows are
kept; common tight rows simply restrict to zero inequalities. -/
lemma mem_commonFace_coord_iff
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    q ∈ Hpoly (commonFaceA a b u x) (commonFaceB a b u x) ↔
      commonFacePoint a b u x q ∈ commonFace a b u x := by
  rw [mem_commonFace_iff_sub_mem_commonDirection]
  constructor
  · intro hq
    refine ⟨?_, ?_⟩
    · intro i
      have hi := hq i
      rw [commonFace_inner_restricted] at hi
      dsimp [commonFaceB] at hi
      dsimp [commonFacePoint]
      rw [inner_add_right]
      linarith
    · rw [commonFacePoint_sub]
      exact commonFaceLift_mem_direction a b u x q
  · rintro ⟨hp, _hdir⟩
    intro i
    have hi := hp i
    rw [commonFace_inner_restricted]
    dsimp [commonFaceB, commonFacePoint] at hi ⊢
    rw [inner_add_right] at hi
    linarith

lemma commonFacePoint_injective
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    Function.Injective (commonFacePoint a b u x) := by
  intro p q hpq
  apply (commonFaceLift a b u x).injective
  have := congrArg (fun z => z - u) hpq
  simpa [commonFacePoint] using this

/-- Every point of the common face has a unique coordinate preimage. -/
lemma commonFacePoint_surjOn
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    Set.SurjOn (commonFacePoint a b u x)
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x))
      (commonFace a b u x) := by
  intro y hy
  have hdir : y - u ∈ commonDirection a b u x :=
    (mem_commonFace_iff_sub_mem_commonDirection a b u x y).1 hy |>.2
  let wy : commonDirection a b u x := ⟨y - u, hdir⟩
  let q := commonFaceRepr a b u x wy
  have hpoint : commonFacePoint a b u x q = y := by
    change u + (((commonFaceRepr a b u x).symm
      ((commonFaceRepr a b u x) wy) : commonDirection a b u x) :
      EuclideanSpace ℝ (Fin d)) = y
    rw [(commonFaceRepr a b u x).symm_apply_apply]
    change u + (y - u) = y
    abel
  have hq : q ∈ Hpoly (commonFaceA a b u x) (commonFaceB a b u x) :=
    (mem_commonFace_coord_iff a b u x q).2 (hpoint ▸ hy)
  exact ⟨q, hq, hpoint⟩

/-- Boundedness transfers to the lower-dimensional coordinate polytope because
`commonFacePoint q = u + lift q` and `lift` is an isometry. -/
lemma commonFace_coord_bounded
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) :
    Bornology.IsBounded
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) := by
  obtain ⟨C, hC⟩ := hbd.exists_norm_le
  refine (isBounded_iff_forall_norm_le).2
    ⟨max 0 (C + ‖u‖), fun q hq => ?_⟩
  have hpF := (mem_commonFace_coord_iff a b u x q).1 hq
  have hp : commonFacePoint a b u x q ∈ Hpoly a b := hpF.1
  have hCp := hC _ hp
  have hlift : ‖commonFaceLift a b u x q‖ = ‖q‖ :=
    (commonFaceLift a b u x).norm_map q
  have htri : ‖commonFaceLift a b u x q‖ ≤
      ‖commonFacePoint a b u x q‖ + ‖u‖ := by
    have h := norm_sub_le (commonFacePoint a b u x q) u
    simpa [commonFacePoint] using h
  have hmain : ‖q‖ ≤ C + ‖u‖ := by
    rw [← hlift]
    linarith
  exact hmain.trans (le_max_right _ _)

end HirschPolynomialAccess
end
end

-- BEGIN Solutions.PolynomialCircuitLocalization
section

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

noncomputable def sourceOnlyRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, u⟫ = b i ∧ ⟪a i, v⟫ ≠ b i)

noncomputable def targetOnlyRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i =>
    a i ≠ 0 ∧ ⟪a i, u⟫ ≠ b i ∧ ⟪a i, v⟫ = b i)

noncomputable def circuitNeutralRows
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, g⟫ = 0)

/-- The common-face direction space injects into the rows tight only at the
source vertex. Consequently its dimension is bounded by the number of such
rows. No simplicity or irredundancy hypothesis is needed. -/
theorem commonFaceDim_le_sourceOnlyRows_card
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b)) :
    commonFaceDim a b u v ≤ (sourceOnlyRows a b u v).card := by
  classical
  let C := commonSourceRows a b u v
  let S := sourceOnlyRows a b u v
  let W := commonDirection a b u v
  let T : W →ₗ[ℝ] (S → ℝ) := (rowEvalMap a S).domRestrict W
  have hTin : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    let q : W := y - z
    have hTq : T q = 0 := by
      change T (y - z) = 0
      rw [map_sub, hyz, sub_self]
    have hqC : ∀ i, i ∈ C →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      have hker : rowEvalMap a C (q : EuclideanSpace ℝ (Fin d)) = 0 := by
        apply LinearMap.mem_ker.1
        exact q.property
      exact congrFun hker ⟨i, hi⟩
    have hqS : ∀ i, i ∈ S →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      change T q ⟨i, hi⟩ = 0
      exact congrFun hTq ⟨i, hi⟩
    have hqtight : ∀ i, ⟪a i, u⟫ = b i →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hiu
      by_cases hai : a i = 0
      · simp [hai]
      by_cases hiv : ⟪a i, v⟫ = b i
      · exact hqC i (by simp [C, commonSourceRows, hai, hiu, hiv])
      · exact hqS i (by simp [S, sourceOnlyRows, hai, hiu, hiv])
    have hq0 := HirschPolynomialAccess.vertex_tight_rows_span_checked
      d n a b u hu (q : EuclideanSpace ℝ (Fin d)) hqtight
    change (y : EuclideanSpace ℝ (Fin d)) -
      (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
    exact sub_eq_zero.mp hq0
  have hle := LinearMap.finrank_le_finrank_of_injective hTin
  simpa [commonFaceDim, W, S] using hle

/-- The same common-face direction space injects into the rows tight only at
the target vertex. -/
theorem commonFaceDim_le_targetOnlyRows_card
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hv : v ∈ extremePoints ℝ (Hpoly a b)) :
    commonFaceDim a b u v ≤ (targetOnlyRows a b u v).card := by
  classical
  let C := commonSourceRows a b u v
  let S := targetOnlyRows a b u v
  let W := commonDirection a b u v
  let T : W →ₗ[ℝ] (S → ℝ) := (rowEvalMap a S).domRestrict W
  have hTin : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    let q : W := y - z
    have hTq : T q = 0 := by
      change T (y - z) = 0
      rw [map_sub, hyz, sub_self]
    have hqC : ∀ i, i ∈ C →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      have hker : rowEvalMap a C (q : EuclideanSpace ℝ (Fin d)) = 0 := by
        apply LinearMap.mem_ker.1
        exact q.property
      exact congrFun hker ⟨i, hi⟩
    have hqS : ∀ i, i ∈ S →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      change T q ⟨i, hi⟩ = 0
      exact congrFun hTq ⟨i, hi⟩
    have hqtight : ∀ i, ⟪a i, v⟫ = b i →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hiv
      by_cases hai : a i = 0
      · simp [hai]
      by_cases hiu : ⟪a i, u⟫ = b i
      · exact hqC i (by simp [C, commonSourceRows, hai, hiu, hiv])
      · exact hqS i (by simp [S, targetOnlyRows, hai, hiu, hiv])
    have hq0 := HirschPolynomialAccess.vertex_tight_rows_span_checked
      d n a b v hv (q : EuclideanSpace ℝ (Fin d)) hqtight
    change (y : EuclideanSpace ℝ (Fin d)) -
      (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
    exact sub_eq_zero.mp hq0
  have hle := LinearMap.finrank_le_finrank_of_injective hTin
  simpa [commonFaceDim, W, S] using hle

/-- A row-circuit direction has at least `d-1` distinct nonzero neutral rows
as soon as one endpoint is a vertex. This is a cardinality consequence of
support minimality; no irredundancy or simplicity assumption is used. -/
theorem circuitNeutralRows_card_ge_dim_sub_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u g : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hg : IsRowCircuit a g) :
    d - 1 ≤ (circuitNeutralRows a g).card := by
  classical
  by_cases hd : d ≤ 1
  · omega
  have hd2 : 2 ≤ d := by omega
  let Z := circuitNeutralRows a g
  by_contra hcard
  have hZlt : Z.card < d - 1 := Nat.lt_of_not_ge hcard
  have hex : ∃ i : Fin n, ⟪a i, g⟫ ≠ 0 := by
    by_contra hn
    have hall : ∀ i : Fin n, ⟪a i, g⟫ = 0 := by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    have hg0 := HirschPolynomialAccess.vertex_tight_rows_span_checked
      d n a b u hu g (fun i _ => hall i)
    exact hg.1 hg0
  obtain ⟨i0, hi0g⟩ := hex
  have hi0a : a i0 ≠ 0 := by
    intro hi0
    rw [hi0, inner_zero_left] at hi0g
    exact hi0g rfl
  have hi0Z : i0 ∉ Z := by
    simp [Z, circuitNeutralRows, hi0a, hi0g]
  let S : Finset (Fin n) := insert i0 Z
  have hScard : S.card = Z.card + 1 := by
    simp [S, hi0Z]
  have hSlt : S.card < d := by
    rw [hScard]
    omega
  let T : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] (S → ℝ) := rowEvalMap a S
  have hnotinj : ¬ Function.Injective T := by
    intro hinj
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    have hcod : Module.finrank ℝ (S → ℝ) = S.card := by
      simp [Fintype.card_coe]
    rw [hdom, hcod] at hle
    omega
  have hker : T.ker ≠ ⊥ := by
    intro hk
    apply hnotinj
    rw [← LinearMap.ker_eq_bot]
    exact hk
  obtain ⟨h, hhker, hh0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hTh : T h = 0 := LinearMap.mem_ker.1 hhker
  have hsub : circuitRowSupport a h ⊆ circuitRowSupport a g := by
    intro i hi
    change ⟪a i, h⟫ ≠ 0 at hi
    change ⟪a i, g⟫ ≠ 0
    intro hig
    have hai : a i ≠ 0 := by
      intro ha0
      rw [ha0, inner_zero_left] at hi
      exact hi rfl
    have hiZ : i ∈ Z := by
      simp [Z, circuitNeutralRows, hai, hig]
    have hiS : i ∈ S := by
      simp [S, hiZ]
    have hcoord := congrFun hTh ⟨i, hiS⟩
    change ⟪a i, h⟫ = 0 at hcoord
    exact hi hcoord
  have hrev := hg.2 h hh0 hsub
  have hi0supp : i0 ∈ circuitRowSupport a g := by
    exact hi0g
  have hi0hsupp := hrev hi0supp
  change ⟪a i0, h⟫ ≠ 0 at hi0hsupp
  have hi0S : i0 ∈ S := by simp [S]
  have hi0zero := congrFun hTh ⟨i0, hi0S⟩
  change ⟪a i0, h⟫ = 0 at hi0zero
  exact hi0hsupp hi0zero

/-- Sharp row-count localization for a vertex-to-vertex row-circuit
displacement. In subtraction-free form:

`2 * dim F(u,v) + d ≤ n + 1`.

Here `commonFaceDim` is the rank-correct dimension of the common-source face.
No simplicity, irredundancy, strict feasibility, or maximal-step hypothesis is
required beyond the two vertex assumptions and the row-circuit property. -/
theorem rowCircuit_commonFaceDim_localization
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    2 * commonFaceDim a b u v + d ≤ n + 1 := by
  classical
  let S := sourceOnlyRows a b u v
  let T := targetOnlyRows a b u v
  let Z := circuitNeutralRows a (v - u)
  have hSdim : commonFaceDim a b u v ≤ S.card := by
    simpa [S] using commonFaceDim_le_sourceOnlyRows_card a b u v hu
  have hTdim : commonFaceDim a b u v ≤ T.card := by
    simpa [T] using commonFaceDim_le_targetOnlyRows_card a b u v hv
  have hZdim : d - 1 ≤ Z.card := by
    simpa [Z] using circuitNeutralRows_card_ge_dim_sub_one a b u (v - u) hu hcirc
  have hST : Disjoint S T := by
    refine Finset.disjoint_left.2 ?_
    intro i hiS hiT
    have hs := (Finset.mem_filter.1 hiS).2
    have ht := (Finset.mem_filter.1 hiT).2
    exact ht.2.1 hs.2.1
  have hSZ : Disjoint S Z := by
    refine Finset.disjoint_left.2 ?_
    intro i hiS hiZ
    have hs := (Finset.mem_filter.1 hiS).2
    have hz := (Finset.mem_filter.1 hiZ).2
    have hz0 : ⟪a i, v - u⟫ = 0 := hz.2
    rw [inner_sub_right] at hz0
    have hvEq : ⟪a i, v⟫ = b i := by linarith [hs.2.1]
    exact hs.2.2 hvEq
  have hTZ : Disjoint T Z := by
    refine Finset.disjoint_left.2 ?_
    intro i hiT hiZ
    have ht := (Finset.mem_filter.1 hiT).2
    have hz := (Finset.mem_filter.1 hiZ).2
    have hz0 : ⟪a i, v - u⟫ = 0 := hz.2
    rw [inner_sub_right] at hz0
    have huEq : ⟪a i, u⟫ = b i := by linarith [ht.2.2]
    exact ht.2.1 huEq
  have hSTZ : Disjoint (S ∪ T) Z := Finset.disjoint_union_left.2 ⟨hSZ, hTZ⟩
  have htotal : (S ∪ T ∪ Z).card ≤ n := by
    have hsub : S ∪ T ∪ Z ⊆ (Finset.univ : Finset (Fin n)) := by simp
    calc
      (S ∪ T ∪ Z).card ≤ (Finset.univ : Finset (Fin n)).card :=
        Finset.card_le_card hsub
      _ = n := by simp
  rw [Finset.card_union_of_disjoint hSTZ,
      Finset.card_union_of_disjoint hST] at htotal
  omega

/-- Equivalent excess-style corollary of the subtraction-free localization
bound. -/
theorem rowCircuit_commonFaceDim_twice_le_excess_add_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    2 * commonFaceDim a b u v ≤ n - d + 1 := by
  have hloc := rowCircuit_commonFaceDim_localization a b u v hu hv hcirc
  have hd : d ≤ n := by
    have hrows := HirschPolynomialAccess.nonzero_tight_rows_card_ge_dim a b u hu
    have hsub :
        (Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, u⟫ = b i)).card ≤ n := by
      calc
        _ ≤ (Finset.univ : Finset (Fin n)).card :=
          Finset.card_le_card (by simp)
        _ = n := by simp
    exact hrows.trans hsub
  omega


end HirschCircuitLocalization
end
end

-- BEGIN Solutions.PolynomialCircuitNeutralRank
section

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- For a row-circuit direction based at an extreme point, the common kernel of
all nonzero rows neutral on the direction is exactly the line spanned by that
direction. This upgrades the previous neutral-row cardinality estimate to the
rank characterization used in circuit geometry. -/
theorem rowCircuit_neutral_kernel_eq_span
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u g : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hg : IsRowCircuit a g) :
    (rowEvalMap a (circuitNeutralRows a g)).ker =
      Submodule.span ℝ ({g} : Set (EuclideanSpace ℝ (Fin d))) := by
  classical
  let Z := circuitNeutralRows a g
  have hex : ∃ i : Fin n, ⟪a i, g⟫ ≠ 0 := by
    by_contra hn
    have hall : ∀ i : Fin n, ⟪a i, g⟫ = 0 := by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    have hg0 := vertex_tight_rows_span_checked
      d n a b u hu g (fun i _ => hall i)
    exact hg.1 hg0
  obtain ⟨i0, hi0g⟩ := hex
  apply le_antisymm
  · intro h hhker
    by_cases hh0 : h = 0
    · subst h
      exact Submodule.zero_mem _
    have hEval : rowEvalMap a Z h = 0 := by
      apply LinearMap.mem_ker.1
      simpa [Z] using hhker
    have hsub : circuitRowSupport a h ⊆ circuitRowSupport a g := by
      intro i hi
      change ⟪a i, h⟫ ≠ 0 at hi
      change ⟪a i, g⟫ ≠ 0
      intro hig
      have hai : a i ≠ 0 := by
        intro hai
        rw [hai, inner_zero_left] at hi
        exact hi rfl
      have hiZ : i ∈ Z := by
        simp [Z, circuitNeutralRows, hai, hig]
      have hzero := congrFun hEval ⟨i, hiZ⟩
      change ⟪a i, h⟫ = 0 at hzero
      exact hi hzero
    let c : ℝ := ⟪a i0, h⟫ / ⟪a i0, g⟫
    let k : EuclideanSpace ℝ (Fin d) := h - c • g
    have hkSub : circuitRowSupport a k ⊆ circuitRowSupport a g := by
      intro i hi
      change ⟪a i, k⟫ ≠ 0 at hi
      change ⟪a i, g⟫ ≠ 0
      intro hig
      have hhig : ⟪a i, h⟫ = 0 := by
        by_contra hhne
        have hiH : i ∈ circuitRowSupport a h := by
          exact hhne
        have hiG := hsub hiH
        change ⟪a i, g⟫ ≠ 0 at hiG
        exact hiG hig
      have hkig : ⟪a i, k⟫ = 0 := by
        dsimp [k]
        rw [inner_sub_right, inner_smul_right, hhig, hig]
        ring
      exact hi hkig
    by_cases hk0 : k = 0
    · have heq : h = c • g := sub_eq_zero.mp hk0
      rw [heq]
      exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton g))
    · have hrev := hg.2 k hk0 hkSub
      have hi0G : i0 ∈ circuitRowSupport a g := by
        exact hi0g
      have hi0K := hrev hi0G
      change ⟪a i0, k⟫ ≠ 0 at hi0K
      have hi0zero : ⟪a i0, k⟫ = 0 := by
        dsimp [k, c]
        rw [inner_sub_right, inner_smul_right, div_mul_cancel₀ _ hi0g]
        exact sub_self _
      exact (hi0K hi0zero).elim
  · apply Submodule.span_le.2
    intro h hh
    have heq : h = g := by simpa using hh
    subst h
    apply LinearMap.mem_ker.2
    funext i
    change ⟪a i.1, g⟫ = 0
    exact (Finset.mem_filter.1 i.2).2.2

/-- Rank-nullity form of `rowCircuit_neutral_kernel_eq_span`: the nonzero rows
neutral on a row-circuit direction have linear rank exactly `d-1`. -/
theorem rowCircuit_neutral_rank_eq_dim_sub_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u g : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hg : IsRowCircuit a g) :
    Module.finrank ℝ (rowEvalMap a (circuitNeutralRows a g)).range = d - 1 := by
  let T := rowEvalMap a (circuitNeutralRows a g)
  have hker : T.ker = Submodule.span ℝ ({g} : Set (EuclideanSpace ℝ (Fin d))) := by
    simpa [T] using rowCircuit_neutral_kernel_eq_span a b u g hu hg
  have hkerRank : Module.finrank ℝ T.ker = 1 := by
    rw [hker]
    exact finrank_span_singleton hg.1
  have hrank := T.finrank_range_add_finrank_ker
  have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  rw [hkerRank, hdom] at hrank
  have hrank' := congrArg (fun m : ℕ => m - 1) hrank
  simpa using hrank'


end HirschCircuitLocalization
end
end

-- BEGIN Solutions.PolynomialCircuitFaceNeutralRank
section

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- Restricting all ambient neutral rows of a row circuit to any subspace that
contains the circuit direction leaves exactly the same one-dimensional kernel,
now viewed inside that subspace. -/
theorem rowCircuit_neutral_kernel_on_subspace_eq_span
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u g : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hg : IsRowCircuit a g)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hgW : g ∈ W) :
    ((rowEvalMap a (circuitNeutralRows a g)).domRestrict W).ker =
      Submodule.span ℝ
        ({⟨g, hgW⟩} : Set W) := by
  classical
  let R := rowEvalMap a (circuitNeutralRows a g)
  let gw : W := ⟨g, hgW⟩
  have hamb : R.ker =
      Submodule.span ℝ ({g} : Set (EuclideanSpace ℝ (Fin d))) := by
    simpa [R] using rowCircuit_neutral_kernel_eq_span a b u g hu hg
  apply le_antisymm
  · intro x hx
    have hxamb : (x : EuclideanSpace ℝ (Fin d)) ∈ R.ker := by
      apply LinearMap.mem_ker.2
      have hx0 := LinearMap.mem_ker.1 hx
      simpa [R] using hx0
    rw [hamb] at hxamb
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxamb
    apply Submodule.mem_span_singleton.mpr
    refine ⟨c, ?_⟩
    apply Subtype.ext
    simpa [gw] using hc
  · apply Submodule.span_le.2
    intro x hx
    have hxgw : x = gw := by simpa [gw] using hx
    subst x
    apply LinearMap.mem_ker.2
    funext i
    change ⟪a i.1, g⟫ = 0
    exact (Finset.mem_filter.1 i.2).2.2

/-- Rank form of `rowCircuit_neutral_kernel_on_subspace_eq_span`: on every
subspace containing the circuit direction, the ambient neutral rows have rank
exactly one less than the dimension of that subspace. -/
theorem rowCircuit_neutral_rank_on_subspace_eq_dim_sub_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u g : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hg : IsRowCircuit a g)
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hgW : g ∈ W) :
    Module.finrank ℝ
        (((rowEvalMap a (circuitNeutralRows a g)).domRestrict W).range) =
      Module.finrank ℝ W - 1 := by
  let T := (rowEvalMap a (circuitNeutralRows a g)).domRestrict W
  let gw : W := ⟨g, hgW⟩
  have hker : T.ker = Submodule.span ℝ ({gw} : Set W) := by
    simpa [T, gw] using
      rowCircuit_neutral_kernel_on_subspace_eq_span a b u g hu hg W hgW
  have hgw0 : gw ≠ 0 := by
    intro h
    apply hg.1
    have hv := congrArg Subtype.val h
    simpa [gw] using hv
  have hkerRank : Module.finrank ℝ T.ker = 1 := by
    rw [hker]
    exact finrank_span_singleton hgw0
  have hrank := T.finrank_range_add_finrank_ker
  rw [hkerRank] at hrank
  have hrank' := congrArg (fun m : ℕ => m - 1) hrank
  simpa using hrank'

/-- Central rank fact for intrinsic common-face restriction. If `v-u` is an
ambient row circuit based at the vertex `u`, then all ambient rows neutral on
that displacement, restricted to the direction space of the minimal common
face of `u` and `v`, have rank exactly `commonFaceDim - 1`.

This is the rank-preservation input used before deleting intrinsically
redundant restricted inequalities in the circuit-defect accounting argument. -/
theorem rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    Module.finrank ℝ
        (((rowEvalMap a (circuitNeutralRows a (v - u))).domRestrict
          (commonDirection a b u v)).range) =
      commonFaceDim a b u v - 1 := by
  have hgW : v - u ∈ commonDirection a b u v := by
    apply LinearMap.mem_ker.2
    funext i
    have hi := (Finset.mem_filter.1 i.2).2
    change ⟪a i.1, v - u⟫ = 0
    rw [inner_sub_right, hi.2.2, hi.2.1, sub_self]
  simpa [commonFaceDim] using
    rowCircuit_neutral_rank_on_subspace_eq_dim_sub_one
      a b u (v - u) hu hcirc (commonDirection a b u v) hgW


end HirschCircuitLocalization
end
end

-- BEGIN Solutions.PolynomialRowRankDeletion
section

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- Deleting rows from a restricted row-evaluation system lowers its linear
rank by no more than the number of deleted rows. This is the finite-dimensional
rank-loss estimate needed when passing from all restricted ambient inequalities
to a selected irredundant face presentation. -/
theorem restricted_rowEval_rank_le_subrank_add_deleted
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (S T : Finset (Fin n))
    (hST : S ⊆ T) :
    Module.finrank ℝ (((rowEvalMap a T).domRestrict W).range) ≤
      Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) +
        (T \ S).card := by
  classical
  let D := T \ S
  let A := (rowEvalMap a S).domRestrict W
  let B := (rowEvalMap a D).domRestrict W
  let Q := (rowEvalMap a T).domRestrict W
  let P : W →ₗ[ℝ] A.range × (D → ℝ) :=
    LinearMap.prod A.rangeRestrict B
  have hker : P.ker = Q.ker := by
    ext x
    constructor
    · intro hx
      have hp0 : P x = 0 := LinearMap.mem_ker.1 hx
      change (A.rangeRestrict x, B x) = (0, 0) at hp0
      have hA0 : A x = 0 := by
        have hfst : A.rangeRestrict x = 0 := congrArg Prod.fst hp0
        exact congrArg Subtype.val hfst
      have hB0 : B x = 0 := congrArg Prod.snd hp0
      apply LinearMap.mem_ker.2
      funext i
      change ⟪a i.1, (x : EuclideanSpace ℝ (Fin d))⟫ = 0
      by_cases hiS : i.1 ∈ S
      · exact congrFun hA0 ⟨i.1, hiS⟩
      · have hiD : i.1 ∈ D := by
          exact Finset.mem_sdiff.mpr ⟨i.2, hiS⟩
        exact congrFun hB0 ⟨i.1, hiD⟩
    · intro hx
      have hQ0 : Q x = 0 := LinearMap.mem_ker.1 hx
      apply LinearMap.mem_ker.2
      change (A.rangeRestrict x, B x) = (0, 0)
      apply Prod.ext
      · apply Subtype.ext
        funext i
        change ⟪a i.1, (x : EuclideanSpace ℝ (Fin d))⟫ = 0
        exact congrFun hQ0 ⟨i.1, hST i.2⟩
      · funext i
        change ⟪a i.1, (x : EuclideanSpace ℝ (Fin d))⟫ = 0
        have hiT : i.1 ∈ T := (Finset.mem_sdiff.1 i.2).1
        exact congrFun hQ0 ⟨i.1, hiT⟩
  have hPnull := P.finrank_range_add_finrank_ker
  have hQnull := Q.finrank_range_add_finrank_ker
  rw [hker] at hPnull
  have hrankEq : Module.finrank ℝ P.range = Module.finrank ℝ Q.range := by
    exact Nat.add_right_cancel (hPnull.trans hQnull.symm)
  have hbound : Module.finrank ℝ P.range ≤
      Module.finrank ℝ A.range + D.card := by
    calc
      Module.finrank ℝ P.range ≤
          Module.finrank ℝ (A.range × (D → ℝ)) :=
        Submodule.finrank_le _
      _ = Module.finrank ℝ A.range + D.card := by
        simp [Fintype.card_coe]
  have hmain : Module.finrank ℝ Q.range ≤
      Module.finrank ℝ A.range + D.card := by
    rw [← hrankEq]
    exact hbound
  simpa [Q, A, D] using hmain

/-- Defect form of the same estimate: if the larger restricted row system has
rank `h-1`, then the missing rank after keeping only `S` is bounded by the
number of removed rows. -/
theorem restricted_rowEval_defect_le_deleted
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (S T : Finset (Fin n))
    (hST : S ⊆ T)
    (hfull : Module.finrank ℝ (((rowEvalMap a T).domRestrict W).range) =
      Module.finrank ℝ W - 1) :
    (Module.finrank ℝ W - 1) -
        Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) ≤
      (T \ S).card := by
  have hle := restricted_rowEval_rank_le_subrank_add_deleted a W S T hST
  rw [hfull] at hle
  omega


end HirschCircuitLocalization
end
end

-- BEGIN Solutions.PolynomialCommonFaceEffectiveRows
section

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- Ambient rows whose normal restricts nontrivially to a chosen linear
subspace. These are exactly the rows that can contribute rank after passing to
that subspace. -/
noncomputable def effectiveRowsOnSubspace
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d))) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i =>
    ∃ x : W, ⟪a i, (x : EuclideanSpace ℝ (Fin d))⟫ ≠ 0)

/-- Removing rows that vanish identically on `W` does not change the kernel of
the row-evaluation map restricted to `W`. -/
theorem restricted_rowEval_effective_kernel_eq
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (S : Finset (Fin n)) :
    ((rowEvalMap a (S ∩ effectiveRowsOnSubspace a W)).domRestrict W).ker =
      ((rowEvalMap a S).domRestrict W).ker := by
  classical
  let E := effectiveRowsOnSubspace a W
  let A := (rowEvalMap a (S ∩ E)).domRestrict W
  let B := (rowEvalMap a S).domRestrict W
  change A.ker = B.ker
  ext x
  constructor
  · intro hx
    have hA0 : A x = 0 := LinearMap.mem_ker.1 hx
    apply LinearMap.mem_ker.2
    funext i
    change ⟪a i.1, (x : EuclideanSpace ℝ (Fin d))⟫ = 0
    by_cases hiE : i.1 ∈ E
    · have hiSE : i.1 ∈ S ∩ E := Finset.mem_inter.2 ⟨i.2, hiE⟩
      exact congrFun hA0 ⟨i.1, hiSE⟩
    · have hnone : ¬ ∃ y : W,
          ⟪a i.1, (y : EuclideanSpace ℝ (Fin d))⟫ ≠ 0 := by
        simpa [E, effectiveRowsOnSubspace] using hiE
      by_contra hne
      exact hnone ⟨x, hne⟩
  · intro hx
    have hB0 : B x = 0 := LinearMap.mem_ker.1 hx
    apply LinearMap.mem_ker.2
    funext i
    change ⟪a i.1, (x : EuclideanSpace ℝ (Fin d))⟫ = 0
    exact congrFun hB0 ⟨i.1, (Finset.mem_inter.1 i.2).1⟩

/-- Rank version of `restricted_rowEval_effective_kernel_eq`. -/
theorem restricted_rowEval_effective_rank_eq
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (W : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (S : Finset (Fin n)) :
    Module.finrank ℝ
        (((rowEvalMap a (S ∩ effectiveRowsOnSubspace a W)).domRestrict W).range) =
      Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) := by
  let A := (rowEvalMap a (S ∩ effectiveRowsOnSubspace a W)).domRestrict W
  let B := (rowEvalMap a S).domRestrict W
  have hker : A.ker = B.ker := by
    simpa [A, B] using restricted_rowEval_effective_kernel_eq a W S
  have hA := A.finrank_range_add_finrank_ker
  have hB := B.finrank_range_add_finrank_ker
  rw [hker] at hA
  exact Nat.add_right_cancel (hA.trans hB.symm)

/-- The rows that remain nontrivial on the common-face direction satisfy the
basic ambient count budget

`effective rows + ambient dimension ≤ original rows + common-face dimension`.

No vertex, circuit, irredundancy, or boundedness assumption is needed: this is
purely the rank-nullity cost of imposing the common tight equations. -/
theorem commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    (effectiveRowsOnSubspace a (commonDirection a b u v)).card + d ≤
      n + commonFaceDim a b u v := by
  classical
  let C := commonSourceRows a b u v
  let W := commonDirection a b u v
  let E := effectiveRowsOnSubspace a W
  let T := rowEvalMap a C
  have hCE : Disjoint C E := by
    refine Finset.disjoint_left.2 ?_
    intro i hiC hiE
    have hex : ∃ x : W,
        ⟪a i, (x : EuclideanSpace ℝ (Fin d))⟫ ≠ 0 := by
      simpa [E, effectiveRowsOnSubspace] using hiE
    obtain ⟨x, hx⟩ := hex
    have hxker : (x : EuclideanSpace ℝ (Fin d)) ∈ T.ker := by
      simpa [T, W, C, commonDirection] using x.property
    have hzero : T (x : EuclideanSpace ℝ (Fin d)) = 0 :=
      LinearMap.mem_ker.1 hxker
    have hcoord := congrFun hzero ⟨i, hiC⟩
    exact hx hcoord
  have htotal : C.card + E.card ≤ n := by
    have hcard : (C ∪ E).card = C.card + E.card :=
      Finset.card_union_of_disjoint hCE
    have hsub : C ∪ E ⊆ (Finset.univ : Finset (Fin n)) := by simp
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    simpa using hle
  have hnull : Module.finrank ℝ T.range + Module.finrank ℝ W = d := by
    have h := T.finrank_range_add_finrank_ker
    have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
      finrank_euclideanSpace_fin (𝕜 := ℝ)
    rw [hdom] at h
    simpa [T, W, C, commonDirection] using h
  have hrange : Module.finrank ℝ T.range ≤ C.card := by
    calc
      Module.finrank ℝ T.range ≤ Module.finrank ℝ (C → ℝ) :=
        Submodule.finrank_le _
      _ = C.card := by simp [Fintype.card_coe]
  have hdim : d ≤ C.card + Module.finrank ℝ W := by omega
  have hmain : E.card + d ≤ n + Module.finrank ℝ W := by omega
  simpa [E, W, commonFaceDim] using hmain

/-- On a common face of a row-circuit pair, discarding ambient rows that become
identically zero does not change the exact neutral rank `h-1`. -/
theorem rowCircuit_effectiveNeutral_rank_on_commonDirection_eq_faceDim_sub_one
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u)) :
    Module.finrank ℝ
        (((rowEvalMap a
          (circuitNeutralRows a (v - u) ∩
            effectiveRowsOnSubspace a (commonDirection a b u v))).domRestrict
          (commonDirection a b u v)).range) =
      commonFaceDim a b u v - 1 := by
  rw [restricted_rowEval_effective_rank_eq]
  exact rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one
    a b u v hu hcirc


end HirschCircuitLocalization
end
end

-- BEGIN Solutions.PolynomialCircuitSelectedRowDefect
section

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- Row-level defect/excess budget for a vertex-to-vertex ambient row circuit.

Let `W` be the direction space of the minimal common face of `u,v`, let `E` be
the ambient rows that restrict nontrivially to `W`, and choose any `F ⊆ E`.
The neutral-rank defect left after retaining only the rows of `F` is charged by
the rows of `E` that were discarded. Combining this with the common-face row
count gives the subtraction-free inequality

`|F| + defect(F) + d ≤ n + dim W`.

If a later geometric lemma chooses one row of `F` for each true facet of the
common face, this specializes exactly to `(f-h)+delta ≤ n-d`. -/
theorem rowCircuit_selectedEffectiveRows_defect_budget
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b u v)) :
    F.card +
        ((commonFaceDim a b u v - 1) -
          Module.finrank ℝ
            (((rowEvalMap a (F ∩ circuitNeutralRows a (v - u))).domRestrict
              (commonDirection a b u v)).range)) +
        d ≤
      n + commonFaceDim a b u v := by
  classical
  let W := commonDirection a b u v
  let E := effectiveRowsOnSubspace a W
  let Z := circuitNeutralRows a (v - u)
  let T := Z ∩ E
  let S := F ∩ Z
  have hST : S ⊆ T := by
    intro i hiS
    have hi := Finset.mem_inter.1 hiS
    exact Finset.mem_inter.2 ⟨hi.2, hF hi.1⟩
  have hfull :
      Module.finrank ℝ (((rowEvalMap a T).domRestrict W).range) =
        Module.finrank ℝ W - 1 := by
    simpa [T, Z, E, W, commonFaceDim] using
      rowCircuit_effectiveNeutral_rank_on_commonDirection_eq_faceDim_sub_one
        a b u v hu hcirc
  have hdef :
      (Module.finrank ℝ W - 1) -
          Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) ≤
        (T \ S).card :=
    restricted_rowEval_defect_le_deleted a W S T hST hfull
  have hdelSub : T \ S ⊆ E \ F := by
    intro i hi
    have hiTS := Finset.mem_sdiff.1 hi
    have hiT := Finset.mem_inter.1 hiTS.1
    apply Finset.mem_sdiff.2
    refine ⟨hiT.2, ?_⟩
    intro hiFmem
    apply hiTS.2
    exact Finset.mem_inter.2 ⟨hiFmem, hiT.1⟩
  have hdel : (T \ S).card ≤ (E \ F).card :=
    Finset.card_le_card hdelSub
  have hdefE :
      (Module.finrank ℝ W - 1) -
          Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range) ≤
        (E \ F).card :=
    hdef.trans hdel
  have hbudget : E.card + d ≤ n + Module.finrank ℝ W := by
    simpa [E, W, commonFaceDim] using
      commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim a b u v
  have hF' : F ⊆ E := by simpa [E, W] using hF
  have hcard : (E \ F).card + F.card = E.card :=
    Finset.card_sdiff_add_card_eq_card hF'
  have hmain :
      F.card +
          ((Module.finrank ℝ W - 1) -
            Module.finrank ℝ (((rowEvalMap a S).domRestrict W).range)) +
          d ≤
        n + Module.finrank ℝ W := by
    omega
  simpa [S, Z, W, commonFaceDim] using hmain

/-- Rearranged form of `rowCircuit_selectedEffectiveRows_defect_budget`, stated
in the traditional facet-excess style. The premises `dim W ≤ |F|` and `d ≤ n`
make both natural-number subtractions genuine differences. They hold for the
intended application where `F` is a full-dimensional genuine-facet
presentation of the common face. -/
theorem rowCircuit_selectedEffectiveRows_excess_defect
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hcirc : IsRowCircuit a (v - u))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b u v))
    (hface : commonFaceDim a b u v ≤ F.card)
    (hdn : d ≤ n) :
    (F.card - commonFaceDim a b u v) +
        ((commonFaceDim a b u v - 1) -
          Module.finrank ℝ
            (((rowEvalMap a (F ∩ circuitNeutralRows a (v - u))).domRestrict
              (commonDirection a b u v)).range)) ≤
      n - d := by
  have h := rowCircuit_selectedEffectiveRows_defect_budget
    a b u v hu hcirc F hF
  omega


end HirschCircuitLocalization
end
end

-- BEGIN Solutions.PolynomialCircuitDefectPublicBridge
section

open scoped RealInnerProductSpace InnerProduct
open Set Module Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschCircuitLocalization

open HirschPolynomialAccess

variable {d n : ℕ}

/-- A row restricts nontrivially to the common-direction subspace exactly when
its canonical common-face coordinate normal is nonzero. -/
theorem effectiveRowsOn_commonDirection_eq_coordinateEffectiveRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    effectiveRowsOnSubspace a (commonDirection a b u v) =
      Finset.univ.filter (fun i => commonFaceA a b u v i ≠ 0) := by
  classical
  ext i
  simp only [effectiveRowsOnSubspace, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx⟩ hA0
    let q := commonFaceRepr a b u v x
    have hinner := commonFace_inner_restricted a b u v i q
    have hlift : commonFaceLift a b u v q =
        (x : EuclideanSpace ℝ (Fin d)) := by
      change (((commonFaceRepr a b u v).symm
        ((commonFaceRepr a b u v) x) : commonDirection a b u v) :
        EuclideanSpace ℝ (Fin d)) =
        (x : EuclideanSpace ℝ (Fin d))
      rw [(commonFaceRepr a b u v).symm_apply_apply]
    rw [hA0, inner_zero_left, hlift] at hinner
    exact hx hinner.symm
  · intro hA
    let q := commonFaceA a b u v i
    let x : commonDirection a b u v :=
      ⟨commonFaceLift a b u v q,
        commonFaceLift_mem_direction a b u v q⟩
    refine ⟨x, ?_⟩
    change ⟪a i, commonFaceLift a b u v q⟫ ≠ 0
    rw [← commonFace_inner_restricted a b u v i q]
    dsimp [q]
    exact inner_self_ne_zero.mpr hA

/-- The internal effective-row set agrees definitionally with the already
public common-face effective-row vocabulary. -/
theorem effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v : EuclideanSpace ℝ (Fin d)) :
    effectiveRowsOnSubspace a (commonDirection a b u v) =
      HirschCommonFace.commonFaceEffectiveRows a b u v := by
  rw [effectiveRowsOn_commonDirection_eq_coordinateEffectiveRows]
  rfl


end HirschCircuitLocalization
end
end

-- BEGIN Solutions.CircuitSlackTranslation
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

theorem circuitRowSupport_eq_support_rowMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (g : EuclideanSpace ℝ (Fin d)) :
    circuitRowSupport a g = Function.support (rowMap a g) := by
  ext i
  rfl

theorem slack_nonneg_iff_mem_Hpoly {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    (∀ i, 0 ≤ slack a b x i) ↔ x ∈ Hpoly a b := by
  constructor
  · intro h i
    have hi := h i
    dsimp [slack] at hi
    linarith
  · intro h i
    have hi := h i
    dsimp [slack]
    linarith

theorem slack_mem_SlackPoly_iff {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x : EuclideanSpace ℝ (Fin d)) :
    slack a b x ∈ SlackPoly a b ↔ x ∈ Hpoly a b := by
  constructor
  · intro h
    exact (slack_nonneg_iff_mem_Hpoly a b x).mp h.2
  · intro hx
    refine ⟨⟨x, rfl⟩, ?_⟩
    exact (slack_nonneg_iff_mem_Hpoly a b x).mpr hx

theorem slack_sub_slack_eq_rowMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) :
    slack a b x - slack a b y = rowMap a (y - x) := by
  funext i
  simp only [Pi.sub_apply, slack, rowMap, LinearMap.coe_mk, AddHom.coe_mk,
    inner_sub_right]
  ring

theorem slack_line {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d)) (t : ℝ) :
    slack a b (x + t • (y - x)) =
      slack a b x + t • (slack a b y - slack a b x) := by
  funext i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, slack,
    inner_add_right, inner_smul_right, inner_sub_right]
  ring

theorem slack_injective_of_rowMap_injective {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a)) :
    Function.Injective (slack a b) := by
  intro x y hxy
  apply hinj
  funext i
  have hi := congrFun hxy i
  simp only [slack] at hi
  change ⟪a i, x⟫ = ⟪a i, y⟫
  linarith

theorem isRowCircuit_iff_elementary_rowMap {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d))
    (hinj : Function.Injective (rowMap a))
    (g : EuclideanSpace ℝ (Fin d)) :
    IsRowCircuit a g ↔
      IsElementaryIn (LinearMap.range (rowMap a)) (rowMap a g) := by
  constructor
  · rintro ⟨hg0, hmin⟩
    refine ⟨?_, ⟨g, rfl⟩, ?_⟩
    · intro hz
      apply hg0
      apply hinj
      simpa using hz
    · intro w hw0 hwRange hsub
      rcases hwRange with ⟨h, rfl⟩
      have hh0 : h ≠ 0 := by
        intro hh
        subst h
        simp at hw0
      have hsub' : circuitRowSupport a h ⊆ circuitRowSupport a g := by
        simpa [circuitRowSupport_eq_support_rowMap] using hsub
      have hout := hmin h hh0 hsub'
      simpa [circuitRowSupport_eq_support_rowMap] using hout
  · rintro ⟨hmap0, _hRange, hmin⟩
    refine ⟨?_, ?_⟩
    · intro hg0
      subst g
      exact hmap0 (by simp)
    · intro h hh0 hsub
      have hmh0 : rowMap a h ≠ 0 := by
        intro hz
        apply hh0
        apply hinj
        simpa using hz
      have hsub' : Function.support (rowMap a h) ⊆
          Function.support (rowMap a g) := by
        simpa [circuitRowSupport_eq_support_rowMap] using hsub
      have hout := hmin (rowMap a h) hmh0 ⟨h, rfl⟩ hsub'
      simpa [circuitRowSupport_eq_support_rowMap] using hout

theorem rowCircuitStep_iff_slackCircuitStep {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (x y : EuclideanSpace ℝ (Fin d)) :
    RowCircuitStep a b x y ↔
      SlackCircuitStep a b (slack a b x) (slack a b y) := by
  constructor
  · rintro ⟨hx, hy, hcirc, hmax⟩
    refine ⟨(slack_mem_SlackPoly_iff a b x).mpr hx,
      (slack_mem_SlackPoly_iff a b y).mpr hy, ?_, ?_⟩
    · rw [slack_sub_slack_eq_rowMap]
      exact (isRowCircuit_iff_elementary_rowMap a hinj (y - x)).mp hcirc
    · intro t ht hmem
      have hline := slack_line a b x y t
      rw [← hline] at hmem
      exact hmax t ht ((slack_mem_SlackPoly_iff a b _).mp hmem)
  · rintro ⟨hx, hy, hcirc, hmax⟩
    refine ⟨(slack_mem_SlackPoly_iff a b x).mp hx,
      (slack_mem_SlackPoly_iff a b y).mp hy, ?_, ?_⟩
    · rw [slack_sub_slack_eq_rowMap] at hcirc
      exact (isRowCircuit_iff_elementary_rowMap a hinj (y - x)).mpr hcirc
    · intro t ht hfeas
      apply hmax t ht
      have hmem := (slack_mem_SlackPoly_iff a b _).mpr hfeas
      rw [slack_line a b x y t] at hmem
      exact hmem

theorem rowCircuitWalk_to_slackCircuitWalk {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hinj : Function.Injective (rowMap a))
    (L : ℕ) (u v : EuclideanSpace ℝ (Fin d)) :
    RowCircuitWalk a b L u v →
      SlackCircuitWalk a b L (slack a b u) (slack a b v) := by
  rintro ⟨w, hw0, hwL, hfeas, hstep⟩
  refine ⟨fun j => slack a b (w j), ?_, ?_, ?_, ?_⟩
  · simpa [hw0]
  · simpa [hwL]
  · intro j hj
    exact (slack_mem_SlackPoly_iff a b (w j)).mpr (hfeas j hj)
  · intro j hj
    rcases hstep j hj with hstay | hmove
    · left
      simpa [hstay]
    · right
      exact (rowCircuitStep_iff_slackCircuitStep a b hinj (w j) (w (j + 1))).mp hmove


end HirschCircuit
end

-- BEGIN Solutions.CircuitSlackBounded
section

set_option autoImplicit false
set_option maxHeartbeats 2000000
open scoped RealInnerProductSpace
open Hirsch

namespace HirschCircuit

/-- A nonempty bounded H-polytope has no nonzero direction annihilated by every
row.  Equivalently, its row-evaluation map is injective. -/
theorem rowMap_injective_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hb : Bornology.IsBounded (Hpoly a b))
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ Hpoly a b) :
    Function.Injective (rowMap a) := by
  intro p q hpq
  by_contra hpqne
  have hdiff : p - q ≠ 0 := sub_ne_zero.mpr hpqne
  have hnorm : 0 < ‖p - q‖ := norm_pos_iff.mpr hdiff
  have hker : rowMap a (p - q) = 0 := by
    rw [map_sub, hpq, sub_self]
  have hline : ∀ t : ℝ, x + t • (p - q) ∈ Hpoly a b := by
    intro t i
    have hki : ⟪a i, p - q⟫ = 0 := by
      have hi := congrFun hker i
      simpa [rowMap] using hi
    have hxi := hx i
    simpa [inner_add_right, inner_smul_right, hki] using hxi
  obtain ⟨r, hr⟩ := hb.subset_closedBall x
  let t : ℝ := (r + 1) / ‖p - q‖
  have hr0 : 0 ≤ r := by
    have hball0 := Metric.mem_closedBall.mp (hr hx)
    simpa using hball0
  have ht : 0 < t := by
    dsimp [t]
    exact div_pos (by linarith) hnorm
  have hball := Metric.mem_closedBall.mp (hr (hline t))
  have hdist : dist (x + t • (p - q)) x = r + 1 := by
    rw [dist_eq_norm]
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    dsimp [t]
    field_simp [ne_of_gt hnorm]
  rw [hdist] at hball
  linarith


end HirschCircuit
end

-- BEGIN Solutions.PolynomialCircuitBoundedNeutralRank
section

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- A bounded nonempty H-polyhedron has at least ambient-dimension many rows.
Unlike `rows_ge_dimension_of_vertex`, no extreme-point hypothesis is needed. -/
theorem rows_ge_dimension_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Hpoly a b) :
    d ≤ n := by
  have hinj := HirschCircuit.rowMap_injective_of_bounded a b hbd u hu
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  have hcod : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  rw [hdom, hcod] at hle
  exact hle

/-- Boundedness, rather than vertexhood of the source checkpoint, is enough to
show that the rows neutral on a row-circuit direction have common kernel exactly
the circuit line. -/
theorem rowCircuit_neutral_kernel_eq_span_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Hpoly a b)
    (g : EuclideanSpace ℝ (Fin d))
    (hg : IsRowCircuit a g) :
    (rowEvalMap a (circuitNeutralRows a g)).ker =
      Submodule.span ℝ ({g} : Set (EuclideanSpace ℝ (Fin d))) := by
  classical
  let Z := circuitNeutralRows a g
  have hinj := HirschCircuit.rowMap_injective_of_bounded a b hbd u hu
  have hex : ∃ i : Fin n, ⟪a i, g⟫ ≠ 0 := by
    by_contra hn
    have hall : ∀ i : Fin n, ⟪a i, g⟫ = 0 := by
      intro i
      by_contra hi
      exact hn ⟨i, hi⟩
    have hmap : HirschCircuit.rowMap a g = HirschCircuit.rowMap a 0 := by
      funext i
      simp [HirschCircuit.rowMap, hall i]
    exact hg.1 (hinj hmap)
  obtain ⟨i0, hi0g⟩ := hex
  apply le_antisymm
  · intro h hhker
    by_cases hh0 : h = 0
    · subst h
      exact Submodule.zero_mem _
    have hEval : rowEvalMap a Z h = 0 := by
      apply LinearMap.mem_ker.1
      simpa [Z] using hhker
    have hsub : circuitRowSupport a h ⊆ circuitRowSupport a g := by
      intro i hi
      change ⟪a i, h⟫ ≠ 0 at hi
      change ⟪a i, g⟫ ≠ 0
      intro hig
      have hai : a i ≠ 0 := by
        intro hai
        rw [hai, inner_zero_left] at hi
        exact hi rfl
      have hiZ : i ∈ Z := by
        simp [Z, circuitNeutralRows, hai, hig]
      have hzero := congrFun hEval ⟨i, hiZ⟩
      change ⟪a i, h⟫ = 0 at hzero
      exact hi hzero
    let c : ℝ := ⟪a i0, h⟫ / ⟪a i0, g⟫
    let k : EuclideanSpace ℝ (Fin d) := h - c • g
    have hkSub : circuitRowSupport a k ⊆ circuitRowSupport a g := by
      intro i hi
      change ⟪a i, k⟫ ≠ 0 at hi
      change ⟪a i, g⟫ ≠ 0
      intro hig
      have hhig : ⟪a i, h⟫ = 0 := by
        by_contra hhne
        have hiH : i ∈ circuitRowSupport a h := hhne
        have hiG := hsub hiH
        change ⟪a i, g⟫ ≠ 0 at hiG
        exact hiG hig
      have hkig : ⟪a i, k⟫ = 0 := by
        dsimp [k]
        rw [inner_sub_right, inner_smul_right, hhig, hig]
        ring
      exact hi hkig
    by_cases hk0 : k = 0
    · have heq : h = c • g := sub_eq_zero.mp hk0
      rw [heq]
      exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton g))
    · have hrev := hg.2 k hk0 hkSub
      have hi0G : i0 ∈ circuitRowSupport a g := hi0g
      have hi0K := hrev hi0G
      change ⟪a i0, k⟫ ≠ 0 at hi0K
      have hi0zero : ⟪a i0, k⟫ = 0 := by
        dsimp [k, c]
        rw [inner_sub_right, inner_smul_right, div_mul_cancel₀ _ hi0g]
        exact sub_self _
      exact (hi0K hi0zero).elim
  · apply Submodule.span_le.2
    intro h hh
    have heq : h = g := by simpa using hh
    subst h
    apply LinearMap.mem_ker.2
    funext i
    change ⟪a i.1, g⟫ = 0
    exact (Finset.mem_filter.1 i.2).2.2

/-- Rank-nullity form of the bounded nonvertex neutral-kernel theorem. -/
theorem rowCircuit_neutral_rank_eq_dim_sub_one_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ Hpoly a b)
    (g : EuclideanSpace ℝ (Fin d))
    (hg : IsRowCircuit a g) :
    Module.finrank ℝ (rowEvalMap a (circuitNeutralRows a g)).range = d - 1 := by
  let T := rowEvalMap a (circuitNeutralRows a g)
  have hker : T.ker = Submodule.span ℝ ({g} : Set (EuclideanSpace ℝ (Fin d))) := by
    simpa [T] using rowCircuit_neutral_kernel_eq_span_of_bounded a b hbd u hu g hg
  have hkerRank : Module.finrank ℝ T.ker = 1 := by
    rw [hker]
    exact finrank_span_singleton hg.1
  have hrank := T.finrank_range_add_finrank_ker
  have hdom : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) = d :=
    finrank_euclideanSpace_fin (𝕜 := ℝ)
  rw [hkerRank, hdom] at hrank
  have hrank' := congrArg (fun m : ℕ => m - 1) hrank
  simpa using hrank'

/-- On the common carrier of a row-circuit displacement, ambient neutral rows
still have rank exactly `h-1` when the source checkpoint is merely feasible,
provided the parent is bounded. -/
theorem rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (v - u)) :
    Module.finrank ℝ
        (((rowEvalMap a (circuitNeutralRows a (v - u))).domRestrict
          (commonDirection a b u v)).range) =
      commonFaceDim a b u v - 1 := by
  have hgW : v - u ∈ commonDirection a b u v := by
    apply LinearMap.mem_ker.2
    funext i
    have hi := (Finset.mem_filter.1 i.2).2
    change ⟪a i.1, v - u⟫ = 0
    rw [inner_sub_right, hi.2.2, hi.2.1, sub_self]
  let T := (rowEvalMap a (circuitNeutralRows a (v - u))).domRestrict
    (commonDirection a b u v)
  let gw : commonDirection a b u v := ⟨v - u, hgW⟩
  have hker : T.ker = Submodule.span ℝ ({gw} : Set (commonDirection a b u v)) := by
    apply le_antisymm
    · intro x hx
      have hxamb : (x : EuclideanSpace ℝ (Fin d)) ∈
          (rowEvalMap a (circuitNeutralRows a (v - u))).ker := by
        apply LinearMap.mem_ker.2
        have hx0 := LinearMap.mem_ker.1 hx
        simpa [T] using hx0
      have hamb := rowCircuit_neutral_kernel_eq_span_of_bounded
        a b hbd u hu (v - u) hcirc
      rw [hamb] at hxamb
      obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hxamb
      apply Submodule.mem_span_singleton.mpr
      refine ⟨c, ?_⟩
      apply Subtype.ext
      simpa [gw] using hc
    · apply Submodule.span_le.2
      intro x hx
      have hxgw : x = gw := by simpa [gw] using hx
      subst x
      apply LinearMap.mem_ker.2
      funext i
      change ⟪a i.1, v - u⟫ = 0
      exact (Finset.mem_filter.1 i.2).2.2
  have hgw0 : gw ≠ 0 := by
    intro h
    apply hcirc.1
    have hv := congrArg Subtype.val h
    simpa [gw] using hv
  have hkerRank : Module.finrank ℝ T.ker = 1 := by
    rw [hker]
    exact finrank_span_singleton hgw0
  have hrank := T.finrank_range_add_finrank_ker
  rw [hkerRank] at hrank
  have hrank' := congrArg (fun m : ℕ => m - 1) hrank
  simpa [T, commonFaceDim] using hrank'


end HirschCircuitLocalization
end
end

-- BEGIN Solutions.PolynomialCircuitDeletionSavings
section

/-!
# Exact savings in nonvertex circuit-carrier defect accounting

The old inequality `(|F|-h) + defect <= n-d` drops two kinds of savings:
rows disappearing on the carrier beyond its codimension, and redundant neutral
rank among the effective rows removed from a selected presentation. In
particular, every discarded *nonneutral* effective row saves one full unit.

This file proves an exact three-term slack identity and its strictness/equality
criteria. These are one-carrier accounting theorems, not a monotonicity or
polynomial graph-routing theorem. `F` need not be an equivalent presentation;
when it is a minimum equivalent presentation, existing boundedness lemmas give
`h <= |F|`. Neither endpoint needs to be a vertex.
-/

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace HirschCircuitLocalization

open HirschPolynomialAccess

/-- Keep the neutral-deletion count instead of weakening it to all deletions.
The source is merely feasible; boundedness supplies exact ambient circuit rank. -/
theorem rowCircuit_selected_defect_le_discarded_neutral_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y)) :
    let W := commonDirection a b x y
    let E := effectiveRowsOnSubspace a W
    let Z := circuitNeutralRows a (y - x)
    (commonFaceDim a b x y - 1) -
        Module.finrank ℝ (((rowEvalMap a (F ∩ Z)).domRestrict W).range) ≤
      ((E \ F) ∩ Z).card := by
  classical
  let W := commonDirection a b x y
  let E := effectiveRowsOnSubspace a W
  let Z := circuitNeutralRows a (y - x)
  have hST : F ∩ Z ⊆ Z ∩ E := by
    intro i hi
    exact Finset.mem_inter.2 ⟨(Finset.mem_inter.1 hi).2,
      hF (Finset.mem_inter.1 hi).1⟩
  have hfull : Module.finrank ℝ
      (((rowEvalMap a (Z ∩ E)).domRestrict W).range) =
      Module.finrank ℝ W - 1 := by
    rw [show E = effectiveRowsOnSubspace a W from rfl,
      restricted_rowEval_effective_rank_eq]
    exact rowCircuit_neutral_rank_on_commonDirection_eq_commonFaceDim_sub_one_of_bounded
      a b hbd x y hx hcirc
  have h := restricted_rowEval_defect_le_deleted a W (F ∩ Z) (Z ∩ E) hST hfull
  have heq : (Z ∩ E) \ (F ∩ Z) = (E \ F) ∩ Z := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  rw [heq] at h
  exact h

/-- Exact decomposition of the unused ambient excess into three nonnegative
savings: disappearance surplus `kappa`, discarded nonneutral rows `s`, and
neutral deletion redundancy `t`. All subtractions are justified in the proof.

`e_F + delta + kappa + s + t = n-d`.

A small number of high-excess carriers is NOT sufficient for a polynomial
routing bound: their own graph costs still need an independent bound. -/
theorem rowCircuit_selected_excess_defect_savings_identity_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card) :
    let W := commonDirection a b x y
    let h := commonFaceDim a b x y
    let E := effectiveRowsOnSubspace a W
    let Z := circuitNeutralRows a (y - x)
    let delta := (h - 1) -
      Module.finrank ℝ (((rowEvalMap a (F ∩ Z)).domRestrict W).range)
    (F.card - h) + delta +
      (n + h - (E.card + d)) +
      ((E \ F) \ Z).card + (((E \ F) ∩ Z).card - delta) = n - d := by
  classical
  let W := commonDirection a b x y
  let h := commonFaceDim a b x y
  let E := effectiveRowsOnSubspace a W
  let Z := circuitNeutralRows a (y - x)
  let delta := (h - 1) -
    Module.finrank ℝ (((rowEvalMap a (F ∩ Z)).domRestrict W).range)
  have hdef : delta ≤ ((E \ F) ∩ Z).card :=
    rowCircuit_selected_defect_le_discarded_neutral_of_bounded a b x y hbd hx hcirc F hF
  have hbudget : E.card + d ≤ n + h :=
    commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim a b x y
  have hdn := rows_ge_dimension_of_bounded a b hbd x hx
  have hcard : (E \ F).card + F.card = E.card :=
    Finset.card_sdiff_add_card_eq_card hF
  have hsplit : ((E \ F) \ Z).card + ((E \ F) ∩ Z).card = (E \ F).card :=
    Finset.card_sdiff_add_card_inter (E \ F) Z
  change (F.card - h) + delta + (n + h - (E.card + d)) +
    ((E \ F) \ Z).card + (((E \ F) ∩ Z).card - delta) = n - d
  change h ≤ F.card at hface
  omega

/-- Strengthened resource bound: every omitted nonneutral effective row gives
one extra unit of certified slack beyond presentation excess and neutral defect. -/
theorem rowCircuit_selected_excess_defect_add_nonneutral_savings_le_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card) :
    let W := commonDirection a b x y
    let h := commonFaceDim a b x y
    let E := effectiveRowsOnSubspace a W
    let Z := circuitNeutralRows a (y - x)
    let delta := (h - 1) -
      Module.finrank ℝ (((rowEvalMap a (F ∩ Z)).domRestrict W).range)
    (F.card - h) + delta + ((E \ F) \ Z).card ≤ n - d := by
  have hid := rowCircuit_selected_excess_defect_savings_identity_of_bounded
    a b x y hbd hx hcirc F hF hface
  dsimp only at hid ⊢
  omega

/-- The old budget is saturated precisely when all three explicit savings
vanish. The last equality says every discarded neutral row costs a unit of rank. -/
theorem rowCircuit_selected_budget_saturated_iff_of_bounded
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ effectiveRowsOnSubspace a (commonDirection a b x y))
    (hface : commonFaceDim a b x y ≤ F.card) :
    let W := commonDirection a b x y
    let h := commonFaceDim a b x y
    let E := effectiveRowsOnSubspace a W
    let Z := circuitNeutralRows a (y - x)
    let delta := (h - 1) -
      Module.finrank ℝ (((rowEvalMap a (F ∩ Z)).domRestrict W).range)
    (F.card - h) + delta = n - d ↔
      E.card + d = n + h ∧
      ((E \ F) \ Z).card = 0 ∧
      ((E \ F) ∩ Z).card = delta := by
  have hid := rowCircuit_selected_excess_defect_savings_identity_of_bounded
    a b x y hbd hx hcirc F hF hface
  have hdef := rowCircuit_selected_defect_le_discarded_neutral_of_bounded
    a b x y hbd hx hcirc F hF
  have hbudget := commonDirection_effectiveRows_card_add_dim_le_rows_add_faceDim a b x y
  dsimp only at hid hdef ⊢
  omega


end HirschCircuitLocalization
end
end

-- BEGIN Solutions.PolynomialCircuitDeletionSavingsPublic
section

open scoped BigOperators RealInnerProductSpace InnerProduct
open Set Module Hirsch

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Hirsch

/-- Public-vocabulary form of the exact selected-row savings identity for a
bounded nonvertex row-circuit carrier.

Let `h` be the canonical common-carrier dimension, `E` its public effective-row
set, `Z` the nonzero ambient rows neutral on the circuit displacement, and `F`
a selected subset of `E` with at least `h` rows.  If `delta` is the neutral-rank
defect of `F`, then the entire ambient row excess splits exactly as

`(F.card-h) + delta + kappa + s + tau = n-d`,

where `kappa` is surplus row disappearance, `s` counts omitted nonneutral
effective rows, and `tau` is omitted neutral-row redundancy beyond actual rank
loss.  This is one-carrier accounting, not a routing theorem. -/
theorem standalone_row_circuit_selected_excess_defect_savings_identity
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b x y)
    (hface : HirschCommonFace.commonFaceDim a b x y ≤ F.card) :
    let h := HirschCommonFace.commonFaceDim a b x y
    let E := HirschCommonFace.commonFaceEffectiveRows a b x y
    let Z := Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, y - x⟫ = 0)
    let delta := (h - 1) -
      Module.finrank ℝ
        (((HirschCommonFace.rowEvalMap a (F ∩ Z)).domRestrict
          (HirschCommonFace.commonDirection a b x y)).range)
    (F.card - h) + delta +
      (n + h - (E.card + d)) +
      ((E \ F) \ Z).card + (((E \ F) ∩ Z).card - delta) = n - d := by
  classical
  have hF' :
      F ⊆ HirschCircuitLocalization.effectiveRowsOnSubspace a
        (HirschPolynomialAccess.commonDirection a b x y) := by
    rw [HirschCircuitLocalization.effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows]
    exact hF
  have hface' : HirschPolynomialAccess.commonFaceDim a b x y ≤ F.card := by
    simpa [HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
      HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
      HirschPolynomialAccess.commonFaceDim,
      HirschPolynomialAccess.commonDirection,
      HirschPolynomialAccess.rowEvalMap,
      HirschPolynomialAccess.commonSourceRows] using hface
  have h :=
    HirschCircuitLocalization.rowCircuit_selected_excess_defect_savings_identity_of_bounded
      a b x y hbd hx hcirc F hF' hface'
  dsimp only at h ⊢
  rw [HirschCircuitLocalization.effectiveRowsOn_commonDirection_eq_publicCommonFaceEffectiveRows
    a b x y] at h
  simpa [HirschCircuitLocalization.circuitNeutralRows,
    HirschCommonFace.commonFaceDim, HirschCommonFace.commonDirection,
    HirschCommonFace.rowEvalMap, HirschCommonFace.commonSourceRows,
    HirschPolynomialAccess.commonFaceDim,
    HirschPolynomialAccess.commonDirection,
    HirschPolynomialAccess.rowEvalMap,
    HirschPolynomialAccess.commonSourceRows] using h


end Hirsch
end
end


theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b x y)
    (hface : HirschCommonFace.commonFaceDim a b x y ≤ F.card) :
    let h := HirschCommonFace.commonFaceDim a b x y
    let E := HirschCommonFace.commonFaceEffectiveRows a b x y
    let Z := Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, y - x⟫ = 0)
    let delta := (h - 1) -
      Module.finrank ℝ
        (((HirschCommonFace.rowEvalMap a (F ∩ Z)).domRestrict
          (HirschCommonFace.commonDirection a b x y)).range)
    (F.card - h) + delta +
      (n + h - (E.card + d)) +
      ((E \ F) \ Z).card + (((E \ F) ∩ Z).card - delta) = n - d := by
  exact Hirsch.standalone_row_circuit_selected_excess_defect_savings_identity a b x y hbd hx hcirc F hF hface

#print axioms solution
