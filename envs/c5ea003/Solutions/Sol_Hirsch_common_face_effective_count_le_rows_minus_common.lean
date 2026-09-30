-- Prove2me | solution 1 for Hirsch.common_face_effective_count_le_rows_minus_common
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-09T11:25:29.59492+00:00
-- url     : https://prove2.me/submissions/49221457-5a3f-4a47-a468-e89c75cc8a94

import Definitions.Def_Hirsch_common_face_geometry
import Definitions.Def_Hirsch_model
import Mathlib

-- BEGIN Solutions/PolynomialVertexSpan.lean

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

-- BEGIN Solutions/PolynomialSeparatedRows.lean

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


-- BEGIN Solutions/PolynomialExcessFaceRank.lean

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


-- BEGIN Solutions/PolynomialCommonFace.lean

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


-- BEGIN Solutions/PolynomialCommonFaceCoords.lean

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


-- BEGIN Solutions/PolynomialCommonFaceTransport.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

noncomputable def commonFaceAffineMap
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin (commonFaceDim a b u x)) →ᵃ[ℝ]
      EuclideanSpace ℝ (Fin d) :=
  (commonFaceLift a b u x).toLinearMap.toAffineMap +
    AffineMap.const ℝ _ u

lemma commonFaceAffineMap_apply
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))) :
    commonFaceAffineMap a b u x q = commonFacePoint a b u x q := by
  simp [commonFaceAffineMap, commonFacePoint, add_comm]

lemma commonFace_coord_extreme_of_face_extreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    {q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))}
    (hqF : commonFacePoint a b u x q ∈
      extremePoints ℝ (commonFace a b u x)) :
    q ∈ extremePoints ℝ
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) := by
  let Q := Hpoly (commonFaceA a b u x) (commonFaceB a b u x)
  have hqQ : q ∈ Q := (mem_commonFace_coord_iff a b u x q).2 hqF.1
  refine ⟨hqQ, ?_⟩
  intro p hp r hr hopen
  have hmapopen : commonFacePoint a b u x q ∈
      openSegment ℝ (commonFacePoint a b u x p) (commonFacePoint a b u x r) := by
    rw [← commonFaceAffineMap_apply a b u x q,
      ← commonFaceAffineMap_apply a b u x p,
      ← commonFaceAffineMap_apply a b u x r,
      ← image_openSegment ℝ (commonFaceAffineMap a b u x) p r]
    exact ⟨q, hopen, rfl⟩
  have hpF : commonFacePoint a b u x p ∈ commonFace a b u x :=
    (mem_commonFace_coord_iff a b u x p).1 hp
  have hrF : commonFacePoint a b u x r ∈ commonFace a b u x :=
    (mem_commonFace_coord_iff a b u x r).1 hr
  have heq := hqF.2 hpF hrF hmapopen
  exact commonFacePoint_injective a b u x heq

lemma commonFace_face_extreme_of_coord_extreme
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    {q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))}
    (hq : q ∈ extremePoints ℝ
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x))) :
    commonFacePoint a b u x q ∈
      extremePoints ℝ (commonFace a b u x) := by
  let Q := Hpoly (commonFaceA a b u x) (commonFaceB a b u x)
  have hqF : commonFacePoint a b u x q ∈ commonFace a b u x :=
    (mem_commonFace_coord_iff a b u x q).1 hq.1
  refine ⟨hqF, ?_⟩
  intro y hy z hz hopen
  obtain ⟨p, hpQ, hpy⟩ := commonFacePoint_surjOn a b u x hy
  obtain ⟨r, hrQ, hrz⟩ := commonFacePoint_surjOn a b u x hz
  have hopen' : commonFacePoint a b u x q ∈
      openSegment ℝ (commonFacePoint a b u x p) (commonFacePoint a b u x r) := by
    simpa [hpy, hrz] using hopen
  have himage : commonFacePoint a b u x q ∈
      (commonFaceAffineMap a b u x) '' openSegment ℝ p r := by
    rw [image_openSegment]
    simpa [commonFaceAffineMap_apply] using hopen'
  obtain ⟨s, hsopen, hsq⟩ := himage
  have hsq' : commonFacePoint a b u x s = commonFacePoint a b u x q := by
    simpa [commonFaceAffineMap_apply] using hsq
  have hs : s = q := commonFacePoint_injective a b u x hsq'
  subst s
  have hpq : p = q := hq.2 hpQ hrQ hsopen
  subst p
  simpa using hpy.symm

lemma commonFace_coord_adj_to_face
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    {p q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))}
    (hadj : Adj
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) p q) :
    Adj (commonFace a b u x)
      (commonFacePoint a b u x p) (commonFacePoint a b u x q) := by
  let Q := Hpoly (commonFaceA a b u x) (commonFaceB a b u x)
  have hne : commonFacePoint a b u x p ≠ commonFacePoint a b u x q := by
    intro h
    exact hadj.1 (commonFacePoint_injective a b u x h)
  refine ⟨hne, ?_⟩
  refine ⟨?_, ?_⟩
  · intro y hyseg
    have hyimg : y ∈ (commonFaceAffineMap a b u x) '' segment ℝ p q := by
      rw [image_segment]
      simpa [commonFaceAffineMap_apply] using hyseg
    obtain ⟨r, hrseg, hry⟩ := hyimg
    have hrQ : r ∈ Q := hadj.2.subset hrseg
    have hrF : commonFacePoint a b u x r ∈ commonFace a b u x :=
      (mem_commonFace_coord_iff a b u x r).1 hrQ
    have hry' : commonFacePoint a b u x r = y := by
      simpa only [commonFaceAffineMap_apply] using hry
    exact hry' ▸ hrF
  · intro y hyF z hzF w hwseg hwopen
    obtain ⟨r, hrQ, hry⟩ := commonFacePoint_surjOn a b u x hyF
    obtain ⟨s, hsQ, hsz⟩ := commonFacePoint_surjOn a b u x hzF
    have hwimg : w ∈ (commonFaceAffineMap a b u x) '' segment ℝ p q := by
      rw [image_segment]
      simpa [commonFaceAffineMap_apply] using hwseg
    obtain ⟨t, htseg, htw⟩ := hwimg
    have hopen' : commonFacePoint a b u x t ∈
        openSegment ℝ (commonFacePoint a b u x r) (commonFacePoint a b u x s) := by
      have htw' : commonFacePoint a b u x t = w := by
        simpa [commonFaceAffineMap_apply] using htw
      simpa [hry, hsz, htw'] using hwopen
    have hopenimg : commonFacePoint a b u x t ∈
        (commonFaceAffineMap a b u x) '' openSegment ℝ r s := by
      rw [image_openSegment]
      simpa [commonFaceAffineMap_apply] using hopen'
    obtain ⟨t', ht'open, ht'eq⟩ := hopenimg
    have htt' : t' = t := by
      apply commonFacePoint_injective a b u x
      simpa [commonFaceAffineMap_apply] using ht'eq
    subst t'
    have hrseg : r ∈ segment ℝ p q :=
      hadj.2.left_mem_of_mem_openSegment hrQ hsQ htseg ht'open
    have hryseg : commonFacePoint a b u x r ∈
        segment ℝ (commonFacePoint a b u x p) (commonFacePoint a b u x q) := by
      rw [← commonFaceAffineMap_apply a b u x r,
        ← commonFaceAffineMap_apply a b u x p,
        ← commonFaceAffineMap_apply a b u x q,
        ← image_segment]
      exact ⟨r, hrseg, rfl⟩
    simpa [hry] using hryseg

lemma commonFace_coord_adj_to_parent
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    {p q : EuclideanSpace ℝ (Fin (commonFaceDim a b u x))}
    (hadj : Adj
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) p q) :
    Adj (Hpoly a b)
      (commonFacePoint a b u x p) (commonFacePoint a b u x q) :=
  commonFace_adj_to_parent a b u x (commonFace_coord_adj_to_face a b u x hadj)

end HirschPolynomialAccess
end


-- BEGIN Solutions/PolynomialFaceEffectiveRows.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschPolynomialAccess

/-- Rows whose normals remain nonzero after restriction to the common-face
direction space. All other rows are tautological in common-face coordinates
whenever the source point is feasible. -/
noncomputable def commonFaceEffectiveRows {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => commonFaceA a b u x i ≠ 0)

noncomputable def commonFaceEffectiveCount {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d)) : ℕ :=
  (commonFaceEffectiveRows a b u x).card

lemma commonFaceB_nonneg_of_mem {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) (i : Fin n) :
    0 ≤ commonFaceB a b u x i := by
  dsimp [commonFaceB]
  exact sub_nonneg.mpr (hu i)

theorem exists_commonFace_effective_model {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b) :
    ∃ e : Fin (commonFaceEffectiveCount a b u x) ↪ Fin n,
      Hpoly
        (fun j => commonFaceA a b u x (e j))
        (fun j => commonFaceB a b u x (e j)) =
      Hpoly (commonFaceA a b u x) (commonFaceB a b u x) := by
  classical
  let S := commonFaceEffectiveRows a b u x
  let E : Fin (commonFaceEffectiveCount a b u x) ≃ S := by
    simpa [commonFaceEffectiveCount, S] using (Fintype.equivFin S).symm
  let e : Fin (commonFaceEffectiveCount a b u x) ↪ Fin n :=
    { toFun := fun j => (E j).val
      inj' := by
        intro j k h
        exact E.injective (Subtype.ext h) }
  have hesurj : ∀ i ∈ S,
      ∃ j : Fin (commonFaceEffectiveCount a b u x), e j = i := by
    intro i hi
    refine ⟨E.symm ⟨i, hi⟩, ?_⟩
    change (E (E.symm ⟨i, hi⟩)).val = i
    rw [E.apply_symm_apply]
  refine ⟨e, ?_⟩
  ext q
  constructor
  · intro hq i
    by_cases hi : i ∈ S
    · obtain ⟨j, hj⟩ := hesurj i hi
      have hjq := hq j
      change ⟪commonFaceA a b u x (e j), q⟫ ≤
        commonFaceB a b u x (e j) at hjq
      simpa only [hj] using hjq
    · have hzero : commonFaceA a b u x i = 0 := by
        simpa [S, commonFaceEffectiveRows] using hi
      rw [hzero, inner_zero_left]
      exact commonFaceB_nonneg_of_mem a b u x hu i
  · intro hq j
    exact hq (e j)

def padToBalancedA {r m : ℕ}
    (a : Fin m → EuclideanSpace ℝ (Fin r)) :
    Fin (2 * r) → EuclideanSpace ℝ (Fin r) :=
  fun i => if h : (i : ℕ) < m then a ⟨i, h⟩ else 0

def padToBalancedB {r m : ℕ} (b : Fin m → ℝ) : Fin (2 * r) → ℝ :=
  fun i => if h : (i : ℕ) < m then b ⟨i, h⟩ else 1

lemma hpoly_padToBalanced {r m : ℕ} (hm : m ≤ 2 * r)
    (a : Fin m → EuclideanSpace ℝ (Fin r)) (b : Fin m → ℝ) :
    Hpoly (padToBalancedA a) (padToBalancedB b) = Hpoly a b := by
  ext q
  simp only [Hpoly, mem_setOf_eq, padToBalancedA, padToBalancedB]
  constructor
  · intro h i
    have hi : (i : ℕ) < 2 * r := lt_of_lt_of_le i.isLt hm
    simpa [i.isLt] using h ⟨i, hi⟩
  · intro h i
    by_cases hi : (i : ℕ) < m
    · simpa [hi] using h ⟨i, hi⟩
    · simp [hi, inner_zero_left]

theorem exists_balanced_commonFace_model {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (heff : commonFaceEffectiveCount a b u x ≤ 2 * commonFaceDim a b u x) :
    ∃ a' : Fin (2 * commonFaceDim a b u x) →
          EuclideanSpace ℝ (Fin (commonFaceDim a b u x)),
      ∃ b' : Fin (2 * commonFaceDim a b u x) → ℝ,
        Hpoly a' b' =
          Hpoly (commonFaceA a b u x) (commonFaceB a b u x) := by
  obtain ⟨e, he⟩ := exists_commonFace_effective_model a b u x hu
  let ae := fun j => commonFaceA a b u x (e j)
  let be := fun j => commonFaceB a b u x (e j)
  refine ⟨padToBalancedA ae, padToBalancedB be, ?_⟩
  rw [hpoly_padToBalanced heff ae be]
  exact he

theorem commonFace_coord_diam_of_balanced_effective
    {d n B : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ Hpoly a b)
    (heff : commonFaceEffectiveCount a b u x ≤ 2 * commonFaceDim a b u x)
    (hbalanced : ∀
      (a' : Fin (2 * commonFaceDim a b u x) →
        EuclideanSpace ℝ (Fin (commonFaceDim a b u x)))
      (b' : Fin (2 * commonFaceDim a b u x) → ℝ),
      (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
      DiamLE (Hpoly a' b') B)
    (hne : (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)).Nonempty)
    (hbd : Bornology.IsBounded
      (Hpoly (commonFaceA a b u x) (commonFaceB a b u x))) :
    DiamLE (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) B := by
  obtain ⟨a', b', hP⟩ := exists_balanced_commonFace_model a b u x hu heff
  have hne' : (Hpoly a' b').Nonempty := by simpa only [hP] using hne
  have hbd' : Bornology.IsBounded (Hpoly a' b') := by simpa only [hP] using hbd
  have hD := hbalanced a' b' hne' hbd'
  simpa only [hP] using hD


end HirschPolynomialAccess
end


-- BEGIN Solutions/PolynomialFaceEffectiveCountBounds.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3500000

noncomputable section

namespace HirschPolynomialAccess

theorem commonFaceA_eq_zero_of_common_row {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) (i : Fin n)
    (hi : i ∈ commonSourceRows a b p q) :
    commonFaceA a b p q i = 0 := by
  let A := commonFaceA a b p q i
  have hlift : commonFaceLift a b p q A ∈ commonDirection a b p q :=
    commonFaceLift_mem_direction a b p q A
  have hker : rowEvalMap a (commonSourceRows a b p q)
      (commonFaceLift a b p q A) = 0 := LinearMap.mem_ker.1 hlift
  have horth : ⟪a i, commonFaceLift a b p q A⟫ = 0 :=
    congrFun hker ⟨i, hi⟩
  have hself : ⟪A, A⟫ = 0 := by
    rw [commonFace_inner_restricted]
    exact horth
  by_contra hA
  exact (ne_of_gt (real_inner_self_pos.mpr hA)) hself

theorem disjoint_effective_common_rows {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) :
    Disjoint (commonFaceEffectiveRows a b p q) (commonSourceRows a b p q) := by
  refine Finset.disjoint_left.2 ?_
  intro i hie hic
  have hne : commonFaceA a b p q i ≠ 0 := by
    simpa [commonFaceEffectiveRows] using hie
  exact hne (commonFaceA_eq_zero_of_common_row a b p q i hic)

theorem commonFaceEffectiveCount_le_sub_common_card {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) :
    commonFaceEffectiveCount a b p q ≤ n - (commonSourceRows a b p q).card := by
  classical
  let E := commonFaceEffectiveRows a b p q
  let C := commonSourceRows a b p q
  have hdisj : Disjoint E C := by
    simpa [E, C] using disjoint_effective_common_rows a b p q
  have htotal : E.card + C.card ≤ n := by
    rw [← Finset.card_union_of_disjoint hdisj]
    have hsub : E ∪ C ⊆ (Finset.univ : Finset (Fin n)) := by simp
    simpa using Finset.card_le_card hsub
  change E.card ≤ n - C.card
  omega


end HirschPolynomialAccess
end


-- BEGIN Solutions/Sol_Hirsch_common_face_effective_count_bound.lean

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- Rows common to the two defining vertices vanish after restriction to the
common-face direction space, so the number of nonzero restricted rows is at
most the total row count minus the number of common rows. -/
theorem solution
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (p q : EuclideanSpace ℝ (Fin d)) :
    HirschCommonFace.commonFaceEffectiveCount a b p q ≤
      n - (HirschCommonFace.commonSourceRows a b p q).card := by
  exact HirschPolynomialAccess.commonFaceEffectiveCount_le_sub_common_card
    a b p q

end


#print axioms solution
