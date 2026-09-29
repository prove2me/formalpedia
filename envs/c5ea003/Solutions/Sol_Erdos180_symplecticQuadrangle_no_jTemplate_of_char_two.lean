-- Prove2me | solution 1 for Erdos180.symplecticQuadrangle_no_jTemplate_of_char_two
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-04T03:17:05.015964+00:00
-- url     : https://prove2.me/submissions/a3a91365-8052-49a4-8299-90b869a4a023

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.CharP.Reduced
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.LinearCombination.Lemmas
import Theorems.Thm_Erdos180_coordinateCenterLine_direction_det_ne_zero_of_ne
import Theorems.Thm_Erdos180_projectiveDirection_nonzero_left
import Theorems.Thm_Erdos180_projectiveDirection_nonzero_right
import Theorems.Thm_Erdos180_symmetricGraphLine_coordinateCenter_common_point_iff
import Theorems.Thm_Erdos180_symplecticAutomorphismLineEquiv_apply
import Theorems.Thm_Erdos180_symplecticAutomorphism_disjoint_iff
import Theorems.Thm_Erdos180_symplecticAutomorphism_incidence_iff
import Theorems.Thm_Erdos180_symplecticLineNormalizer_map_left
import Theorems.Thm_Erdos180_symplecticLineNormalizer_map_right
import Theorems.Thm_Erdos180_symplecticLine_eq_coordinateCenterLine_of_common_points
import Theorems.Thm_Erdos180_symplecticLine_eq_invertible_symmetricGraphLine
import Theorems.Thm_Erdos180_symplecticQuadrangle_no_jTemplate_of_char_two_line_avoidance

namespace Erdos180

section
variable {K : Type*} [CommRing K]

lemma symmetricDet_zero_diagonal_sub (b b' : K) :
    symmetricDet (0 : K) (b - b') 0 = -((b - b') ^ 2) := by
  simp [symmetricDet]

end

section
variable {K : Type*} [Field K] [CharP K 2]

lemma symmetricQuadratic_char_two
    (a b c x y : K) :
    symmetricQuadratic a b c x y = a * x ^ 2 + c * y ^ 2 := by
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp [symmetricQuadratic, htwo]

lemma symmetricQuadratic_char_two_eq_square
    (r s b x y : K) :
    symmetricQuadratic (r ^ 2) b (s ^ 2) x y =
      (r * x + s * y) ^ 2 := by
  rw [symmetricQuadratic_char_two]
  have htwo : (2 : K) = 0 := CharP.cast_eq_zero K 2
  calc
    r ^ 2 * x ^ 2 + s ^ 2 * y ^ 2 =
        (r * x) ^ 2 + (s * y) ^ 2 := by ring
    _ = (r * x + s * y) ^ 2 := by
      rw [add_sq]
      simp [htwo]

lemma square_surjective_char_two [Finite K] :
    Function.Surjective (fun x : K => x ^ 2) := by
  intro a
  obtain ⟨r, hr⟩ := (isSquare_of_charTwo' a).exists_sq
  exact ⟨r, hr.symm⟩

lemma symmetricQuadratic_char_two_diagonal_zero_of_two_independent_roots
    [Finite K] {a b c x y x' y' : K}
    (hind : x * y' - x' * y ≠ 0)
    (hfirst : symmetricQuadratic a b c x y = 0)
    (hsecond : symmetricQuadratic a b c x' y' = 0) :
    a = 0 ∧ c = 0 := by
  obtain ⟨r, hr⟩ := square_surjective_char_two a
  obtain ⟨s, hs⟩ := square_surjective_char_two c
  change r ^ 2 = a at hr
  change s ^ 2 = c at hs
  have hlinfirst : r * x + s * y = 0 := by
    apply (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
    rw [← symmetricQuadratic_char_two_eq_square]
    simpa [hr, hs] using hfirst
  have hlinsecond : r * x' + s * y' = 0 := by
    apply (pow_eq_zero_iff (by norm_num : 2 ≠ 0)).mp
    rw [← symmetricQuadratic_char_two_eq_square]
    simpa [hr, hs] using hsecond
  have hrdet : (x * y' - x' * y) * r = 0 := by
    linear_combination y' * hlinfirst - y * hlinsecond
  have hsdet : (x * y' - x' * y) * s = 0 := by
    linear_combination x * hlinsecond - x' * hlinfirst
  have hrzero : r = 0 := (mul_eq_zero.mp hrdet).resolve_left hind
  have hszero : s = 0 := (mul_eq_zero.mp hsdet).resolve_left hind
  constructor
  · simpa [hrzero] using hr.symm
  · simpa [hszero] using hs.symm

end

section
variable {K : Type*} [Field K]

lemma symmetricDet_zero_diagonal_sub_ne_zero
    {b b' : K} (h : b ≠ b') :
    symmetricDet (0 : K) (b - b') 0 ≠ 0 := by
  rw [symmetricDet_zero_diagonal_sub]
  exact neg_ne_zero.mpr (pow_ne_zero 2 (sub_ne_zero.mpr h))

end

noncomputable section
variable (K : Type*) [Field K]

lemma symmetricGraphLines_disjoint_of_difference_det
    {a b c a' b' c' : K}
    (hdet : symmetricDet (a - a') (b - b') (c - c') ≠ 0) :
    Disjoint (symmetricGraphLine K a b c).1
      (symmetricGraphLine K a' b' c').1 := by
  apply Submodule.disjoint_def.mpr
  intro w hw hw'
  obtain ⟨u, hu⟩ := hw
  obtain ⟨v, hv⟩ := hw'
  have hvector :
      symmetricGraphVector K a b c (u 0) (u 1) =
        symmetricGraphVector K a' b' c' (v 0) (v 1) := by
    exact hu.trans hv.symm
  have hzero := congrFun hvector 0
  have htwo := congrFun hvector 2
  simp [symmetricGraphVector] at hzero htwo
  have huv : u = v := by
    funext i
    fin_cases i
    · exact hzero
    · exact htwo
  subst v
  have hone := congrFun hvector 1
  have hthree := congrFun hvector 3
  simp [symmetricGraphVector] at hone hthree
  have hdetx :
      symmetricDet (a - a') (b - b') (c - c') * u 0 = 0 := by
    unfold symmetricDet
    linear_combination (c - c') * hone - (b - b') * hthree
  have hdety :
      symmetricDet (a - a') (b - b') (c - c') * u 1 = 0 := by
    unfold symmetricDet
    linear_combination -(b - b') * hone + (a - a') * hthree
  have hx : u 0 = 0 :=
    (mul_eq_zero.mp hdetx).resolve_left hdet
  have hy : u 1 = 0 :=
    (mul_eq_zero.mp hdety).resolve_left hdet
  rw [← hu]
  change symmetricGraphVector K a b c (u 0) (u 1) = 0
  funext i
  fin_cases i <;> simp [symmetricGraphVector, hx, hy]

theorem symmetricGraphLine_zero_diagonal_disjoint
    {b b' : K} (h : b ≠ b') :
    Disjoint (symmetricGraphLine K 0 b 0).1
      (symmetricGraphLine K 0 b' 0).1 := by
  apply symmetricGraphLines_disjoint_of_difference_det K
  simpa using symmetricDet_zero_diagonal_sub_ne_zero h

end

noncomputable section
variable (K : Type*) [Field K]
variable [CharP K 2] [Finite K]

lemma symmetricGraphLine_char_two_diagonal_zero_of_actual_centers
    {a b c x y x' y' : K}
    (hind : x * y' - x' * y ≠ 0)
    (hfirst : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x y
            (projectiveDirection_nonzero_left K hind)).1)
    (hsecond : ∃ p : SymplecticPoint K,
      p.1 ≤ (symmetricGraphLine K a b c).1 ∧
        p.1 ≤
          (coordinateCenterLine K x' y'
            (projectiveDirection_nonzero_right K hind)).1) :
    a = 0 ∧ c = 0 := by
  apply symmetricQuadratic_char_two_diagonal_zero_of_two_independent_roots
    hind
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_left K hind)).mp hfirst
  · exact (symmetricGraphLine_coordinateCenter_common_point_iff K
      (projectiveDirection_nonzero_right K hind)).mp hsecond

end

noncomputable section
open SimpleGraph
variable (K : Type*) [Field K] [CharP K 2] [Finite K]

lemma symplecticLine_char_two_canonical_zero_diagonal
    (X : SymplecticLine K)
    (hXH : Disjoint X.1 (symmetricGraphLine K 0 0 0).1)
    (hXV : Disjoint X.1 (symplecticVerticalLine K).1)
    (centers : Fin 2 → SymplecticLine K)
    (hcenters : Function.Injective centers)
    (hH : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (centers i).1)
    (hV : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (centers i).1)
    (hX : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (centers i).1) :
    ∃ b : K, X = symmetricGraphLine K 0 b 0 := by
  classical
  obtain ⟨a, b, c, hXgraph, _⟩ :=
    symplecticLine_eq_invertible_symmetricGraphLine K X hXV hXH
  choose pH hpHH hpHC using hH
  choose pV hpVV hpVC using hV
  have hclass (i : Fin 2) :
      ∃ (x y : K) (hxy : x ≠ 0 ∨ y ≠ 0),
        centers i = coordinateCenterLine K x y hxy :=
    symplecticLine_eq_coordinateCenterLine_of_common_points
      K (centers i) (pH i) (pV i)
      (hpHH i) (hpHC i) (hpVV i) (hpVC i)
  choose x y hxy hrepr using hclass
  have hind : x 0 * y 1 - x 1 * y 0 ≠ 0 := by
    apply coordinateCenterLine_direction_det_ne_zero_of_ne
      K (hxy 0) (hxy 1)
    intro heq
    have hindex : (0 : Fin 2) = 1 := by
      apply hcenters
      exact (hrepr 0).trans (heq.trans (hrepr 1).symm)
    exact (by decide : (0 : Fin 2) ≠ 1) hindex
  have hfirst :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K a b c).1 ∧
          p.1 ≤
            (coordinateCenterLine K (x 0) (y 0)
              (projectiveDirection_nonzero_left K hind)).1 := by
    obtain ⟨p, hpX, hpC⟩ := hX 0
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 0]
      exact hpC
  have hsecond :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K a b c).1 ∧
          p.1 ≤
            (coordinateCenterLine K (x 1) (y 1)
              (projectiveDirection_nonzero_right K hind)).1 := by
    obtain ⟨p, hpX, hpC⟩ := hX 1
    refine ⟨p, ?_, ?_⟩
    · rw [← hXgraph]
      exact hpX
    · rw [← hrepr 1]
      exact hpC
  obtain ⟨ha, hc⟩ :=
    symmetricGraphLine_char_two_diagonal_zero_of_actual_centers
      K hind hfirst hsecond
  refine ⟨b, ?_⟩
  simpa [ha, hc] using hXgraph

omit [CharP K 2] [Finite K] in
lemma symplecticAutomorphism_commonPoint
    (e : SymplecticAutomorphism K)
    (L M : SymplecticLine K)
    (hpoint : ∃ p : SymplecticPoint K,
      p.1 ≤ L.1 ∧ p.1 ≤ M.1) :
    ∃ p : SymplecticPoint K,
      p.1 ≤ (symplecticAutomorphismLine K e L).1 ∧
        p.1 ≤ (symplecticAutomorphismLine K e M).1 := by
  obtain ⟨p, hpL, hpM⟩ := hpoint
  exact ⟨symplecticAutomorphismPoint K e p,
    (symplecticAutomorphism_incidence_iff K e p L).mpr hpL,
    (symplecticAutomorphism_incidence_iff K e p M).mpr hpM⟩

lemma symplecticLine_char_two_disjoint_of_two_common_center_pairs
    (Y Z X X' : SymplecticLine K)
    (hYZ : Disjoint Y.1 Z.1)
    (hXY : Disjoint X.1 Y.1)
    (hXZ : Disjoint X.1 Z.1)
    (hX'Y : Disjoint X'.1 Y.1)
    (hX'Z : Disjoint X'.1 Z.1)
    (hXX' : X ≠ X')
    (C C' : Fin 2 → SymplecticLine K)
    (hCinj : Function.Injective C)
    (hC'inj : Function.Injective C')
    (hCY : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Y.1 ∧ p.1 ≤ (C i).1)
    (hCZ : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Z.1 ∧ p.1 ≤ (C i).1)
    (hCX : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X.1 ∧ p.1 ≤ (C i).1)
    (hC'Y : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Y.1 ∧ p.1 ≤ (C' i).1)
    (hC'Z : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ Z.1 ∧ p.1 ≤ (C' i).1)
    (hC'X : ∀ i : Fin 2,
      ∃ p : SymplecticPoint K,
        p.1 ≤ X'.1 ∧ p.1 ≤ (C' i).1) :
    Disjoint X.1 X'.1 := by
  classical
  let e : SymplecticAutomorphism K :=
    symplecticLineNormalizer K Y Z hYZ
  let Xn : SymplecticLine K := symplecticAutomorphismLine K e X
  let X'n : SymplecticLine K := symplecticAutomorphismLine K e X'
  let Cn : Fin 2 → SymplecticLine K :=
    fun i => symplecticAutomorphismLine K e (C i)
  let C'n : Fin 2 → SymplecticLine K :=
    fun i => symplecticAutomorphismLine K e (C' i)
  have hXH : Disjoint Xn.1 (symmetricGraphLine K 0 0 0).1 := by
    change Disjoint (symplecticAutomorphismLine K e X).1
      (symmetricGraphLine K 0 0 0).1
    rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X Y).mpr hXY
  have hXV : Disjoint Xn.1 (symplecticVerticalLine K).1 := by
    change Disjoint (symplecticAutomorphismLine K e X).1
      (symplecticVerticalLine K).1
    rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X Z).mpr hXZ
  have hX'H : Disjoint X'n.1 (symmetricGraphLine K 0 0 0).1 := by
    change Disjoint (symplecticAutomorphismLine K e X').1
      (symmetricGraphLine K 0 0 0).1
    rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X' Y).mpr hX'Y
  have hX'V : Disjoint X'n.1 (symplecticVerticalLine K).1 := by
    change Disjoint (symplecticAutomorphismLine K e X').1
      (symplecticVerticalLine K).1
    rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
    exact (symplecticAutomorphism_disjoint_iff K e X' Z).mpr hX'Z
  have hCn : Function.Injective Cn := by
    intro i j hij
    apply hCinj
    apply (symplecticAutomorphismLineEquiv K e).injective
    simpa only [symplecticAutomorphismLineEquiv_apply] using hij
  have hC'n : Function.Injective C'n := by
    intro i j hij
    apply hC'inj
    apply (symplecticAutomorphismLineEquiv K e).injective
    simpa only [symplecticAutomorphismLineEquiv_apply] using hij
  have hCnH (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (Cn i).1 := by
    obtain ⟨p, hpY, hpC⟩ := hCY i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Y).mpr hpY
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C i)).mpr hpC
  have hCnV (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (Cn i).1 := by
    obtain ⟨p, hpZ, hpC⟩ := hCZ i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Z).mpr hpZ
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C i)).mpr hpC
  have hCnX (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ Xn.1 ∧ p.1 ≤ (Cn i).1 := by
    exact symplecticAutomorphism_commonPoint K e X (C i) (hCX i)
  have hC'nH (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symmetricGraphLine K 0 0 0).1 ∧
          p.1 ≤ (C'n i).1 := by
    obtain ⟨p, hpY, hpC⟩ := hC'Y i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_left K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Y).mpr hpY
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C' i)).mpr hpC
  have hC'nV (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ (symplecticVerticalLine K).1 ∧
          p.1 ≤ (C'n i).1 := by
    obtain ⟨p, hpZ, hpC⟩ := hC'Z i
    refine ⟨symplecticAutomorphismPoint K e p, ?_, ?_⟩
    · rw [← symplecticLineNormalizer_map_right K Y Z hYZ]
      exact (symplecticAutomorphism_incidence_iff K e p Z).mpr hpZ
    · exact (symplecticAutomorphism_incidence_iff
        K e p (C' i)).mpr hpC
  have hC'nX (i : Fin 2) :
      ∃ p : SymplecticPoint K,
        p.1 ≤ X'n.1 ∧ p.1 ≤ (C'n i).1 := by
    exact symplecticAutomorphism_commonPoint K e X' (C' i) (hC'X i)
  obtain ⟨b, hb⟩ := symplecticLine_char_two_canonical_zero_diagonal
    K Xn hXH hXV Cn hCn hCnH hCnV hCnX
  obtain ⟨b', hb'⟩ := symplecticLine_char_two_canonical_zero_diagonal
    K X'n hX'H hX'V C'n hC'n hC'nH hC'nV hC'nX
  have hbb : b ≠ b' := by
    intro heq
    apply hXX'
    apply (symplecticAutomorphismLineEquiv K e).injective
    simp only [symplecticAutomorphismLineEquiv_apply]
    change Xn = X'n
    rw [hb, hb', heq]
  apply (symplecticAutomorphism_disjoint_iff K e X X').mp
  change Disjoint Xn.1 X'n.1
  rw [hb, hb']
  exact symmetricGraphLine_zero_diagonal_disjoint K hbb

lemma symplecticLine_char_two_pair_avoidance :
    CharTwoLinePairAvoidance K :=
  symplecticLine_char_two_disjoint_of_two_common_center_pairs K

end

end Erdos180

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K] [CharP K 2] [Finite K]

theorem solution
    (hom : jTemplate →g symplecticQuadrangle K)
    (hbase : Function.Injective
      (fun base : Fin 4 => hom (.inl (.inl base))))
    (hcopies : ∀ copy : Fin 2,
      Set.InjOn hom {vertex | InJCopy copy vertex}) :
    False :=
  symplecticQuadrangle_no_jTemplate_of_char_two_line_avoidance
    K (symplecticLine_char_two_pair_avoidance K) hom hbase hcopies
