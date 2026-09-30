-- Prove2me | solution 1 for Hirsch.separated_common_face_split
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-10T02:26:26.85821+00:00
-- url     : https://prove2.me/submissions/79db5c58-ec42-42a5-a466-f65dbe5897d1

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


-- BEGIN Solutions/PolynomialLocalNeutralRank.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 3000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- Only the normals newly active at `x`, not all neutral normals in the
whole description, are needed to bound the common-source direction space.
No separation or extremality assumption on `u` is needed. -/
theorem common_direction_finrank_le_new_active_subspace
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hnew : ∀ i, a i ≠ 0 → ⟪a i, x⟫ = b i →
      ⟪a i, u⟫ ≠ b i → a i ∈ K) :
    Module.finrank ℝ (commonDirection a b u x) ≤ Module.finrank ℝ K := by
  classical
  let W := commonDirection a b u x
  let T : W →ₗ[ℝ] (K →ₗ[ℝ] ℝ) :=
    { toFun := fun q =>
        { toFun := fun k =>
            ⟪(k : EuclideanSpace ℝ (Fin d)), (q : EuclideanSpace ℝ (Fin d))⟫
          map_add' := by
            intro k l
            simp [inner_add_left]
          map_smul' := by
            intro t k
            simp [inner_smul_left] }
      map_add' := by
        intro p q
        ext k
        simp [inner_add_right]
      map_smul' := by
        intro t q
        ext k
        simp [inner_smul_right] }
  have hTinj : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    let q : W := y - z
    have hTq : T q = 0 := by
      change T (y - z) = 0
      rw [map_sub, hyz, sub_self]
    have hqK : ∀ k : K,
        ⟪(k : EuclideanSpace ℝ (Fin d)), (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro k
      have h := congrArg (fun f : K →ₗ[ℝ] ℝ => f k) hTq
      exact h
    have hqCommon : ∀ i, i ∈ commonSourceRows a b u x →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      have hker : rowEvalMap a (commonSourceRows a b u x)
          (q : EuclideanSpace ℝ (Fin d)) = 0 := LinearMap.mem_ker.1 q.property
      exact congrFun hker ⟨i, hi⟩
    have hqTight : ∀ i, ⟪a i, x⟫ = b i →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hix
      by_cases hai : a i = 0
      · rw [hai, inner_zero_left]
      by_cases hiu : ⟪a i, u⟫ = b i
      · exact hqCommon i (by simp [commonSourceRows, hai, hiu, hix])
      · exact hqK ⟨a i, hnew i hai hix hiu⟩
    have hq0 := vertex_tight_rows_span_checked d n a b x hx
      (q : EuclideanSpace ℝ (Fin d)) hqTight
    change (y : EuclideanSpace ℝ (Fin d)) -
      (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
    exact sub_eq_zero.mp hq0
  have hle := LinearMap.finrank_le_finrank_of_injective hTinj
  simpa only [Module.finrank_linearMap_self] using hle

/-- At a target-avoiding vertex, a local subspace containing its active
neutral normals controls its common-source face dimension. The subspace may
be different at every vertex. -/
theorem common_face_dim_le_active_neutral_subspace
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (havoid : ∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i)
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hK : ∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i →
      ⟪a i, v⟫ ≠ b i → ⟪a i, x⟫ = b i → a i ∈ K) :
    commonFaceDim a b u x ≤ Module.finrank ℝ K := by
  apply common_direction_finrank_le_new_active_subspace a b u x hx K
  intro i hai hix hiu
  have hiv : ⟪a i, v⟫ ≠ b i := fun h => havoid i hai h hix
  exact hK i hai hiu hiv hix


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


-- BEGIN Solutions/PolynomialAdjEndpoints.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 2000000

noncomputable section

namespace HirschPolynomialAccess

variable {d : ℕ}

/-- Both endpoints of an `Adj` edge are extreme points of the parent set.
`Adj` stores that the whole segment is an extreme subset; the endpoint fact is
an elementary consequence. -/
lemma adj_right_extreme
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {u z : EuclideanSpace ℝ (Fin d)}
    (hadj : Adj P u z) : z ∈ extremePoints ℝ P := by
  rcases hadj with ⟨huz, hseg⟩
  have hzP : z ∈ P := hseg.subset (right_mem_segment ℝ u z)
  refine ⟨hzP, ?_⟩
  intro x hxP y hyP hzopen
  have hxseg : x ∈ segment ℝ u z :=
    hseg.left_mem_of_mem_openSegment hxP hyP (right_mem_segment ℝ u z) hzopen
  have hyseg : y ∈ segment ℝ u z :=
    hseg.right_mem_of_mem_openSegment hxP hyP (right_mem_segment ℝ u z) hzopen
  obtain ⟨a, b, ha, hb, hab, hx⟩ := hxseg
  obtain ⟨c, e, hc, he, hce, hy⟩ := hyseg
  obtain ⟨s, t, hs, ht, hst, hxy⟩ := hzopen
  have hcoeff : s * a + t * c + (s * b + t * e) = 1 := by
    calc
      s * a + t * c + (s * b + t * e) = s * (a + b) + t * (c + e) := by ring
      _ = s * 1 + t * 1 := by rw [hab, hce]
      _ = 1 := by linarith
  have hlin0 : s • x + t • y - z = 0 := sub_eq_zero.mpr hxy
  rw [← hx, ← hy] at hlin0
  have hrewrite :
      s • (a • u + b • z) + t • (c • u + e • z) - z =
        (s * a + t * c) • u + (s * b + t * e - 1) • z := by
    module
  have hlin1 :
      (s * a + t * c) • u + (s * b + t * e - 1) • z = 0 := by
    rw [← hrewrite]
    exact hlin0
  have hB : s * b + t * e - 1 = -(s * a + t * c) := by
    linarith [hcoeff]
  rw [hB] at hlin1
  have hlin : (s * a + t * c) • (u - z) = 0 := by
    rw [smul_sub, sub_eq_add_neg]
    simpa only [neg_smul] using hlin1
  have hcoef : s * a + t * c = 0 :=
    (smul_eq_zero.mp hlin).resolve_right (sub_ne_zero.mpr huz)
  have ha0 : a = 0 := by
    nlinarith [mul_nonneg ht.le hc]
  have hb1 : b = 1 := by linarith [hab]
  rw [ha0, zero_smul, zero_add, hb1, one_smul] at hx
  exact hx.symm

lemma adj_symm
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {x y : EuclideanSpace ℝ (Fin d)}
    (h : Adj P x y) : Adj P y x := by
  refine ⟨h.1.symm, ?_⟩
  simpa [segment_symm] using h.2

lemma adj_left_extreme
    (P : Set (EuclideanSpace ℝ (Fin d)))
    {x y : EuclideanSpace ℝ (Fin d)}
    (h : Adj P x y) : x ∈ extremePoints ℝ P :=
  adj_right_extreme P (adj_symm P h)

end HirschPolynomialAccess
end


-- BEGIN Solutions/PolynomialLocalRankAccessCore.lean

open scoped RealInnerProductSpace
open Set Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPolynomialAccess

variable {d n : ℕ}

/-- Transport a coordinate-polytope diameter estimate to a walk between two
vertices in their common-source face. All edges remain genuine parent edges. -/
lemma common_face_walk_of_coord_diam
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (B : ℕ)
    (hD : DiamLE (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) B) :
    ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
      w 0 = u ∧ w B = x ∧
      ∀ j < B, w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  let Q := Hpoly (commonFaceA a b u x) (commonFaceB a b u x)
  have huF : u ∈ commonFace a b u x := commonFace_u_mem a b u x hu.1
  have hxF : x ∈ commonFace a b u x := commonFace_x_mem a b u x hx.1
  have huFext : u ∈ extremePoints ℝ (commonFace a b u x) := by
    rw [(commonFace_isExtreme a b u x).extremePoints_eq]
    exact ⟨huF, hu⟩
  have hxFext : x ∈ extremePoints ℝ (commonFace a b u x) := by
    rw [(commonFace_isExtreme a b u x).extremePoints_eq]
    exact ⟨hxF, hx⟩
  obtain ⟨qu, hquQ, hqu⟩ := commonFacePoint_surjOn a b u x huF
  obtain ⟨qx, hqxQ, hqx⟩ := commonFacePoint_surjOn a b u x hxF
  have hquExt : qu ∈ extremePoints ℝ Q :=
    commonFace_coord_extreme_of_face_extreme a b u x (by simpa [hqu] using huFext)
  have hqxExt : qx ∈ extremePoints ℝ Q :=
    commonFace_coord_extreme_of_face_extreme a b u x (by simpa [hqx] using hxFext)
  obtain ⟨wq, hwq0, hwqB, hwqstep⟩ := hD qu hquExt qx hqxExt
  let w : ℕ → EuclideanSpace ℝ (Fin d) :=
    fun j => commonFacePoint a b u x (wq j)
  refine ⟨w, ?_, ?_, ?_⟩
  · dsimp [w]
    rw [hwq0, hqu]
  · dsimp [w]
    rw [hwqB, hqx]
  · intro j hj
    rcases hwqstep j hj with heq | hadj
    · exact Or.inl (congrArg (commonFacePoint a b u x) heq)
    · exact Or.inr (commonFace_coord_adj_to_parent a b u x hadj)

/-- A predicate first attained along a padded walk is attained across a
genuine edge. No diameter estimate is involved in this graph lemma. -/
lemma localRank_first_hit_edge
    {E : Type*} (R : E → E → Prop) (T : E → Prop)
    {B : ℕ} (w : ℕ → E)
    (h0 : ¬ T (w 0)) (hB : T (w B))
    (hstep : ∀ j < B, w j = w (j + 1) ∨ R (w j) (w (j + 1))) :
    ∃ j < B, ¬ T (w j) ∧ T (w (j + 1)) ∧ R (w j) (w (j + 1)) := by
  classical
  have hex : ∃ k : ℕ, k ≤ B ∧ T (w k) := ⟨B, le_rfl, hB⟩
  let k := Nat.find hex
  have hk : k ≤ B ∧ T (w k) := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    apply h0
    simpa [h] using hk.2
  obtain ⟨j, hjk⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hjB : j < B := by omega
  have hjnot : ¬ T (w j) := by
    intro hjT
    have hmin : k ≤ j := Nat.find_min' hex ⟨by omega, hjT⟩
    omega
  have hjnext : T (w (j + 1)) := by simpa [hjk] using hk.2
  have hadj : R (w j) (w (j + 1)) := by
    rcases hstep j hjB with heq | hadj
    · exact False.elim (hjnot (heq ▸ hjnext))
    · exact hadj
  exact ⟨j, hjB, hjnot, hjnext, hadj⟩

/-- The geometric shortening theorem, independent of any conjectural or
imported diameter theorem. Supply connectivity and any uniform diameter
budget `B` in dimensions at most `r`. A rank-at-most-`r` subspace may be chosen
separately at each target-avoiding vertex and need contain only its active
neutral normals. The conclusion is access to SOME target supporting row,
not a prescribed row or the target vertex. -/
theorem target_face_access_of_local_neutral_rank_core
    (d n r B : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (huv : u ≠ v)
    (hlocal : ∀ x ∈ extremePoints ℝ (Hpoly a b),
      (∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i) →
      ∃ K : Submodule ℝ (EuclideanSpace ℝ (Fin d)),
        Module.finrank ℝ K ≤ r ∧
        ∀ i, a i ≠ 0 → ⟪a i, u⟫ ≠ b i → ⟪a i, v⟫ ≠ b i →
          ⟪a i, x⟫ = b i → a i ∈ K)
    (hconnect : ∃ D : ℕ, ∃ wg : ℕ → EuclideanSpace ℝ (Fin d),
      wg 0 = u ∧ wg D = v ∧
      ∀ j < D, wg j = wg (j + 1) ∨ Adj (Hpoly a b) (wg j) (wg (j + 1)))
    (hlow : ∀ (e : ℕ), e ≤ r →
      ∀ (a' : Fin n → EuclideanSpace ℝ (Fin e)) (b' : Fin n → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') B) :
    ∃ (i : Fin n) (z : EuclideanSpace ℝ (Fin d)),
      a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧
      z ∈ extremePoints ℝ (Hpoly a b) ∧ ⟪a i, z⟫ = b i ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  classical
  let P := Hpoly a b
  let T : EuclideanSpace ℝ (Fin d) → Prop := fun y =>
    ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, v⟫ = b i ∧ ⟪a i, y⟫ = b i
  by_cases hTu : T u
  · obtain ⟨i, hai, hiv, hiu⟩ := hTu
    exact ⟨i, u, hai, hiv, hu, hiu, (fun _ => u), rfl, rfl,
      fun _ _ => Or.inl rfl⟩
  have hexTarget : ∃ i : Fin n, a i ≠ 0 ∧ ⟪a i, v⟫ = b i := by
    by_contra hn
    have horth : ∀ i, ⟪a i, v⟫ = b i → ⟪a i, u - v⟫ = 0 := by
      intro i hit
      have hai : a i = 0 := by
        by_contra hne
        exact hn ⟨i, hne, hit⟩
      rw [hai, inner_zero_left]
    have hdiff := vertex_tight_rows_span_checked d n a b v hv (u - v) horth
    exact huv (sub_eq_zero.mp hdiff)
  obtain ⟨it, hait, hitv⟩ := hexTarget
  have hTv : T v := ⟨it, hait, hitv, hitv⟩
  obtain ⟨D, wg, hwg0, hwgD, hwgstep⟩ := hconnect
  have hTstart : ¬ T (wg 0) := by simpa only [hwg0] using hTu
  have hTend : T (wg D) := by simpa only [hwgD] using hTv
  obtain ⟨j, hjD, hxavoid, hztarget, hxz⟩ :=
    localRank_first_hit_edge (Adj P) T wg hTstart hTend hwgstep
  let x := wg j
  let z := wg (j + 1)
  have hxz' : Adj P x z := hxz
  have hxext : x ∈ extremePoints ℝ P := adj_left_extreme P hxz'
  have hzext : z ∈ extremePoints ℝ P := adj_right_extreme P hxz'
  have hxavoid' : ∀ i, a i ≠ 0 → ⟪a i, v⟫ = b i → ⟪a i, x⟫ ≠ b i := by
    intro i hai hiv hix
    exact hxavoid ⟨i, hai, hiv, hix⟩
  obtain ⟨K, hKr, hK⟩ := hlocal x hxext hxavoid'
  have hdim : commonFaceDim a b u x ≤ r :=
    (common_face_dim_le_active_neutral_subspace a b u v x hxext hxavoid' K hK).trans hKr
  have hQne : (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)).Nonempty := by
    obtain ⟨q, hq, _⟩ := commonFacePoint_surjOn a b u x
      (commonFace_u_mem a b u x hu.1)
    exact ⟨q, hq⟩
  have hD : DiamLE (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) B :=
    hlow _ hdim _ _ hQne (commonFace_coord_bounded a b u x hbd)
  obtain ⟨w0, hw00, hw0x, hw0step⟩ :=
    common_face_walk_of_coord_diam a b u x hu hxext B hD
  obtain ⟨i, hai, hiv, hiz⟩ := hztarget
  let w : ℕ → EuclideanSpace ℝ (Fin d) := fun k => if k ≤ B then w0 k else z
  refine ⟨i, z, hai, hiv, hzext, hiz, w, ?_, ?_, ?_⟩
  · change (if 0 ≤ B then w0 0 else z) = u
    rw [if_pos (Nat.zero_le B)]
    exact hw00
  · change (if B + 1 ≤ B then w0 (B + 1) else z) = z
    exact if_neg (by omega)
  · intro k hk
    by_cases hkB : k < B
    · have hk0 : k ≤ B := by omega
      have hk1 : k + 1 ≤ B := by omega
      simpa only [w, if_pos hk0, if_pos hk1] using hw0step k hkB
    · have hkeq : k = B := by omega
      subst k
      have hleft : w B = x := by
        change (if B ≤ B then w0 B else z) = x
        rw [if_pos le_rfl]
        exact hw0x
      have hright : w (B + 1) = z := by
        change (if B + 1 ≤ B then w0 (B + 1) else z) = z
        exact if_neg (by omega)
      exact Or.inr (by simpa only [hleft, hright] using hxz')


end HirschPolynomialAccess
end


-- BEGIN Solutions/PolynomialResidualRank.lean

open scoped RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess

set_option maxHeartbeats 4000000

noncomputable section

namespace HirschPrescribed

/-- Shared active normals may be quotiented out before measuring new rank.
This can be much smaller than the rank of the newly active normals themselves. -/
theorem common_direction_finrank_le_residual_new_subspace
    (d n : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (K : Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hnew : ∀ j, a j ≠ 0 → ⟪a j, x⟫ = b j → ⟪a j, u⟫ ≠ b j →
      a j ∈ K ⊔ Submodule.span ℝ
        (a '' {i | ⟪a i, u⟫ = b i ∧ ⟪a i, x⟫ = b i})) :
    commonFaceDim a b u x ≤ Module.finrank ℝ K := by
  classical
  let W := commonDirection a b u x
  let C := Submodule.span ℝ (a '' {i | ⟪a i, u⟫ = b i ∧ ⟪a i, x⟫ = b i})
  let T : W →ₗ[ℝ] (K →ₗ[ℝ] ℝ) :=
    { toFun := fun q =>
        { toFun := fun k =>
            ⟪(k : EuclideanSpace ℝ (Fin d)), (q : EuclideanSpace ℝ (Fin d))⟫
          map_add' := by intro k l; simp [inner_add_left]
          map_smul' := by intro t k; simp [inner_smul_left] }
      map_add' := by intro p q; ext k; simp [inner_add_right]
      map_smul' := by intro t q; ext k; simp [inner_smul_right] }
  have hTinj : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    let q : W := y - z
    have hTq : T q = 0 := by
      change T (y - z) = 0
      rw [map_sub, hyz, sub_self]
    let A : Submodule ℝ (EuclideanSpace ℝ (Fin d)) :=
      { carrier := {k | ⟪k, (q : EuclideanSpace ℝ (Fin d))⟫ = 0}
        zero_mem' := by
          change ⟪(0 : EuclideanSpace ℝ (Fin d)), (q : EuclideanSpace ℝ (Fin d))⟫ = 0
          exact inner_zero_left _
        add_mem' := by
          intro k l hk hl
          change ⟪k + l, (q : EuclideanSpace ℝ (Fin d))⟫ = 0
          rw [inner_add_left, hk, hl, add_zero]
        smul_mem' := by
          intro t k hk
          change ⟪t • k, (q : EuclideanSpace ℝ (Fin d))⟫ = 0
          rw [real_inner_smul_left, hk, mul_zero] }
    have hKA : K ≤ A := by
      intro k hk
      have h := congrArg (fun f : K →ₗ[ℝ] ℝ => f ⟨k, hk⟩) hTq
      exact h
    have hCA : C ≤ A := by
      apply Submodule.span_le.2
      rintro _ ⟨i, hi, rfl⟩
      change ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0
      by_cases hai : a i = 0
      · rw [hai, inner_zero_left]
      have hiC : i ∈ commonSourceRows a b u x := by
        simp [commonSourceRows, hai, hi.1, hi.2]
      have hker : rowEvalMap a (commonSourceRows a b u x)
          (q : EuclideanSpace ℝ (Fin d)) = 0 := LinearMap.mem_ker.1 q.property
      exact congrFun hker ⟨i, hiC⟩
    have hsumA : K ⊔ C ≤ A := sup_le hKA hCA
    have hqTight : ∀ i, ⟪a i, x⟫ = b i →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hix
      by_cases hai : a i = 0
      · rw [hai, inner_zero_left]
      by_cases hiu : ⟪a i, u⟫ = b i
      · exact hCA (Submodule.subset_span ⟨i, ⟨hiu, hix⟩, rfl⟩)
      · exact hsumA (hnew i hai hix hiu)
    have hq0 := vertex_tight_rows_span_checked d n a b x hx
      (q : EuclideanSpace ℝ (Fin d)) hqTight
    change (y : EuclideanSpace ℝ (Fin d)) -
      (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
    exact sub_eq_zero.mp hq0
  have hle := LinearMap.finrank_le_finrank_of_injective hTinj
  simpa only [Module.finrank_linearMap_self] using hle


end HirschPrescribed
end


-- BEGIN Solutions/PolynomialPrescribedFaceCore.lean

open scoped RealInnerProductSpace
open Set Hirsch HirschPolynomialAccess

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPrescribed

/-- A first-contact shortening theorem for an arbitrary designated target set.
Only predecessors of edges entering that set need a bound on the dimension
of their common-source face. This geometric core has no diameter imports. -/
theorem target_set_access_of_boundary_face_dim_core
    (d n r B : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (T : EuclideanSpace ℝ (Fin d) → Prop) (hTv : T v)
    (hboundary : ∀ x z, Adj (Hpoly a b) x z → ¬ T x → T z →
      commonFaceDim a b u x ≤ r)
    (hconnect : ∃ D : ℕ, ∃ wg : ℕ → EuclideanSpace ℝ (Fin d),
      wg 0 = u ∧ wg D = v ∧
      ∀ j < D, wg j = wg (j + 1) ∨ Adj (Hpoly a b) (wg j) (wg (j + 1)))
    (hlow : ∀ (e : ℕ), e ≤ r →
      ∀ (a' : Fin n → EuclideanSpace ℝ (Fin e)) (b' : Fin n → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧ T z ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  classical
  by_cases hTu : T u
  · exact ⟨u, hu, hTu, (fun _ => u), rfl, rfl, fun _ _ => Or.inl rfl⟩
  obtain ⟨D, wg, hwg0, hwgD, hwgstep⟩ := hconnect
  have hTstart : ¬ T (wg 0) := by simpa only [hwg0] using hTu
  have hTend : T (wg D) := by simpa only [hwgD] using hTv
  obtain ⟨j, hjD, hxavoid, hztarget, hxz⟩ :=
    localRank_first_hit_edge (Adj (Hpoly a b)) T wg hTstart hTend hwgstep
  let x := wg j
  let z := wg (j + 1)
  have hxz' : Adj (Hpoly a b) x z := hxz
  have hxext : x ∈ extremePoints ℝ (Hpoly a b) := adj_left_extreme _ hxz'
  have hzext : z ∈ extremePoints ℝ (Hpoly a b) := adj_right_extreme _ hxz'
  have hdim : commonFaceDim a b u x ≤ r := hboundary x z hxz' hxavoid hztarget
  have hQne : (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)).Nonempty := by
    obtain ⟨q, hq, _⟩ := commonFacePoint_surjOn a b u x
      (commonFace_u_mem a b u x hu.1)
    exact ⟨q, hq⟩
  have hD : DiamLE (Hpoly (commonFaceA a b u x) (commonFaceB a b u x)) B :=
    hlow _ hdim _ _ hQne (commonFace_coord_bounded a b u x hbd)
  obtain ⟨w0, hw00, hw0x, hw0step⟩ :=
    common_face_walk_of_coord_diam a b u x hu hxext B hD
  let w : ℕ → EuclideanSpace ℝ (Fin d) := fun k => if k ≤ B then w0 k else z
  refine ⟨z, hzext, hztarget, w, ?_, ?_, ?_⟩
  · change (if 0 ≤ B then w0 0 else z) = u
    rw [if_pos (Nat.zero_le B)]
    exact hw00
  · change (if B + 1 ≤ B then w0 (B + 1) else z) = z
    exact if_neg (by omega)
  · intro k hk
    by_cases hkB : k < B
    · have hk0 : k ≤ B := by omega
      have hk1 : k + 1 ≤ B := by omega
      simpa only [w, if_pos hk0, if_pos hk1] using hw0step k hkB
    · have hkeq : k = B := by omega
      subst k
      have hleft : w B = x := by
        change (if B ≤ B then w0 B else z) = x
        rw [if_pos le_rfl]
        exact hw0x
      have hright : w (B + 1) = z := by
        change (if B + 1 ≤ B then w0 (B + 1) else z) = z
        exact if_neg (by omega)
      exact Or.inr (by simpa only [hleft, hright] using hxz')


end HirschPrescribed
end


-- BEGIN Solutions/PolynomialFaceDimTradeoff.lean

open scoped RealInnerProductSpace
open Set Module Hirsch

set_option maxHeartbeats 5000000

noncomputable section

namespace HirschPolynomialAccess

/-- The intersection of the two common-direction spaces at `x` is controlled
by the rows tight at neither endpoint. No separation assumption is needed for
this injectivity statement itself. -/
theorem common_direction_intersection_finrank_le_neutral_card
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ extremePoints ℝ (Hpoly a b)) :
    Module.finrank ℝ
      (show Submodule ℝ (EuclideanSpace ℝ (Fin d)) from
        commonDirection a b u x ⊓ commonDirection a b v x) ≤
      (neutralRows a b u v).card := by
  classical
  let U : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := commonDirection a b u x
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := commonDirection a b v x
  let N := neutralRows a b u v
  let W : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := U ⊓ V
  let T : W →ₗ[ℝ] (N → ℝ) := (rowEvalMap a N).domRestrict W
  have hTin : Function.Injective T := by
    intro y z hyz
    apply Subtype.ext
    let q : W := y - z
    have hTq : T q = 0 := by
      change T (y - z) = 0
      rw [map_sub, hyz, sub_self]
    have hqU : ∀ i, i ∈ commonSourceRows a b u x →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      have hker : rowEvalMap a (commonSourceRows a b u x)
          (q : EuclideanSpace ℝ (Fin d)) = 0 := by
        apply LinearMap.mem_ker.1
        exact q.property.1
      exact congrFun hker ⟨i, hi⟩
    have hqV : ∀ i, i ∈ commonSourceRows a b v x →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      have hker : rowEvalMap a (commonSourceRows a b v x)
          (q : EuclideanSpace ℝ (Fin d)) = 0 := by
        apply LinearMap.mem_ker.1
        exact q.property.2
      exact congrFun hker ⟨i, hi⟩
    have hqN : ∀ i, i ∈ N →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hi
      change T q ⟨i, hi⟩ = 0
      exact congrFun hTq ⟨i, hi⟩
    have hqTight : ∀ i, ⟪a i, x⟫ = b i →
        ⟪a i, (q : EuclideanSpace ℝ (Fin d))⟫ = 0 := by
      intro i hix
      by_cases hai : a i = 0
      · simp [hai]
      by_cases hiu : ⟪a i, u⟫ = b i
      · exact hqU i (by simp [commonSourceRows, hai, hiu, hix])
      by_cases hiv : ⟪a i, v⟫ = b i
      · exact hqV i (by simp [commonSourceRows, hai, hiv, hix])
      · exact hqN i (by simp [N, neutralRows, hai, hiu, hiv])
    have hq0 := vertex_tight_rows_span_checked d n a b x hx
      (q : EuclideanSpace ℝ (Fin d)) hqTight
    change (y : EuclideanSpace ℝ (Fin d)) -
      (z : EuclideanSpace ℝ (Fin d)) = 0 at hq0
    exact sub_eq_zero.mp hq0
  have hle := LinearMap.finrank_le_finrank_of_injective hTin
  simpa [W, U, V, N] using hle

/-- For separated extreme endpoints, the overlap of the source- and
target-common direction spaces costs at most the facet excess `n-2d`. -/
theorem common_direction_intersection_finrank_le_excess
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    Module.finrank ℝ
      (show Submodule ℝ (EuclideanSpace ℝ (Fin d)) from
        commonDirection a b u x ⊓ commonDirection a b v x) ≤
      n - 2 * d :=
  (common_direction_intersection_finrank_le_neutral_card a b u v x hx).trans
    (neutral_card_le_excess a b u v hu hv hsep)

/-- Two-sided common-face dimension tradeoff for every intermediate vertex of
a separated source/target pair:

`dim F(u,x) + dim F(v,x) ≤ d + (n - 2d)`.

At exact balance `n=2d` this becomes the clean complementary inequality
`dim F(u,x) + dim F(v,x) ≤ d`. -/
theorem commonFaceDim_add_le_dim_add_excess
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (u v x : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hx : x ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i) :
    commonFaceDim a b u x + commonFaceDim a b v x ≤
      d + (n - 2 * d) := by
  let U : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := commonDirection a b u x
  let V : Submodule ℝ (EuclideanSpace ℝ (Fin d)) := commonDirection a b v x
  have hinter : Module.finrank ℝ
      (U ⊓ V : Submodule ℝ (EuclideanSpace ℝ (Fin d))) ≤ n - 2 * d := by
    simpa [U, V] using
      common_direction_intersection_finrank_le_excess a b u v x hu hv hx hsep
  have hsup : Module.finrank ℝ
      (U ⊔ V : Submodule ℝ (EuclideanSpace ℝ (Fin d))) ≤ d := by
    have h := Submodule.finrank_le (U ⊔ V)
    simpa using h
  change Module.finrank ℝ U + Module.finrank ℝ V ≤ d + (n - 2 * d)
  rw [← Submodule.finrank_sup_add_finrank_inf_eq U V]
  exact Nat.add_le_add hsup hinter

/-- General separated face splitter. Let
`H = d + (n-2d)`. To reach a point whose common face with the target has
dimension at most `H-R`, it is enough to control graph diameter only in
ambient dimensions at most `R-1`.

For balanced instances `H=d`, recovering a symmetric source/target split.
For positive excess the neutral rows account exactly for the extra `n-2d`
slack in the dimension budget. -/
theorem separated_common_face_split_core
    (d n R B : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (hR0 : 1 ≤ R) (hRd : R ≤ d)
    (hconnect : ∃ D : ℕ, ∃ wg : ℕ → EuclideanSpace ℝ (Fin d),
      wg 0 = u ∧ wg D = v ∧
      ∀ j < D, wg j = wg (j + 1) ∨
        Adj (Hpoly a b) (wg j) (wg (j + 1)))
    (hlow : ∀ (e : ℕ), e ≤ R - 1 →
      ∀ (a' : Fin n → EuclideanSpace ℝ (Fin e)) (b' : Fin n → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧
      commonFaceDim a b v z ≤ d + (n - 2 * d) - R ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  let H := d + (n - 2 * d)
  let T : EuclideanSpace ℝ (Fin d) → Prop := fun y =>
    commonFaceDim a b v y ≤ H - R
  have h2d : 2 * d ≤ n :=
    separated_extremes_n_ge_two_d a b u v hu hv hsep
  have hRH : R ≤ H := by
    dsimp [H]
    omega
  have hself : commonFaceDim a b v v = 0 := by
    have hbot : commonDirection a b v v = (⊥ : Submodule ℝ (EuclideanSpace ℝ (Fin d))) := by
      ext q
      constructor
      · intro hq
        have hq0 : q = 0 := by
          apply vertex_tight_rows_span_checked d n a b v hv q
          intro i hiv
          by_cases hai : a i = 0
          · simp [hai]
          · have hiC : i ∈ commonSourceRows a b v v := by
              simp [commonSourceRows, hai, hiv]
            have hker : rowEvalMap a (commonSourceRows a b v v) q = 0 :=
              LinearMap.mem_ker.1 hq
            exact congrFun hker ⟨i, hiC⟩
        simpa [hq0]
      · intro hq
        have hq0 : q = 0 := by simpa using hq
        subst q
        exact (commonDirection a b v v).zero_mem
    rw [commonFaceDim, hbot]
    simp
  have hTv : T v := by
    dsimp [T]
    rw [hself]
    omega
  have hboundary : ∀ x z, Adj (Hpoly a b) x z → ¬ T x → T z →
      commonFaceDim a b u x ≤ R - 1 := by
    intro x z hxz hxT _hzT
    have hxext : x ∈ extremePoints ℝ (Hpoly a b) :=
      adj_left_extreme (Hpoly a b) hxz
    have hsum := commonFaceDim_add_le_dim_add_excess
      a b u v x hu hv hxext hsep
    have hvlarge : H - R < commonFaceDim a b v x := by
      change ¬ commonFaceDim a b v x ≤ H - R at hxT
      exact Nat.lt_of_not_ge hxT
    dsimp [H] at hvlarge
    omega
  simpa [H, T] using
    (HirschPrescribed.target_set_access_of_boundary_face_dim_core
      d n (R - 1) B a b hbd u v hu T hTv hboundary hconnect hlow)


end HirschPolynomialAccess
end


-- BEGIN Solutions/Sol_Hirsch_separated_common_face_split.lean

open scoped RealInnerProductSpace
open Set Hirsch

noncomputable section

/-- For separated extreme endpoints, lower-dimensional diameter control through
`R-1` lets us reach a parent vertex in `B+1` steps whose common face with the
target has dimension at most `d + (n - 2*d) - R`. -/
theorem solution
    (d n R B : ℕ)
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (hbd : Bornology.IsBounded (Hpoly a b))
    (u v : EuclideanSpace ℝ (Fin d))
    (hu : u ∈ extremePoints ℝ (Hpoly a b))
    (hv : v ∈ extremePoints ℝ (Hpoly a b))
    (hsep : ∀ i, a i ≠ 0 →
      ⟪a i, u⟫ ≠ b i ∨ ⟪a i, v⟫ ≠ b i)
    (hR0 : 1 ≤ R) (hRd : R ≤ d)
    (hconnect : ∃ D : ℕ, ∃ wg : ℕ → EuclideanSpace ℝ (Fin d),
      wg 0 = u ∧ wg D = v ∧
      ∀ j < D, wg j = wg (j + 1) ∨
        Adj (Hpoly a b) (wg j) (wg (j + 1)))
    (hlow : ∀ (e : ℕ), e ≤ R - 1 →
      ∀ (a' : Fin n → EuclideanSpace ℝ (Fin e)) (b' : Fin n → ℝ),
        (Hpoly a' b').Nonempty → Bornology.IsBounded (Hpoly a' b') →
        DiamLE (Hpoly a' b') B) :
    ∃ z : EuclideanSpace ℝ (Fin d),
      z ∈ extremePoints ℝ (Hpoly a b) ∧
      HirschCommonFace.commonFaceDim a b v z ≤ d + (n - 2 * d) - R ∧
      ∃ w : ℕ → EuclideanSpace ℝ (Fin d),
        w 0 = u ∧ w (B + 1) = z ∧
        ∀ j < B + 1,
          w j = w (j + 1) ∨ Adj (Hpoly a b) (w j) (w (j + 1)) := by
  have h := HirschPolynomialAccess.separated_common_face_split_core
    d n R B a b hbd u v hu hv hsep hR0 hRd hconnect hlow
  simpa [HirschCommonFace.commonFaceDim,
    HirschCommonFace.commonDirection, HirschCommonFace.rowEvalMap,
    HirschCommonFace.commonSourceRows,
    HirschPolynomialAccess.commonFaceDim,
    HirschPolynomialAccess.commonDirection, HirschPolynomialAccess.rowEvalMap,
    HirschPolynomialAccess.commonSourceRows] using h

end


#print axioms solution
