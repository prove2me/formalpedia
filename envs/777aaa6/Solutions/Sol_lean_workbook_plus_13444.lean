-- Prove2me | solution 1 for lean_workbook_plus_13444
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-06T01:53:59.357592+00:00
-- url     : https://prove2.me/submissions/c638914f-ad22-409a-a838-a53589dc02a4

import Mathlib.RingTheory.Int.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace RationalCubicNineInfinitude

theorem residues {a b c : ℤ} (h : a ^ 3 + b ^ 3 = 9 * c ^ 3)
    (hab : IsCoprime a b) :
    a % 3 ≠ 0 ∧ b % 3 ≠ 0 ∧ a % 3 ≠ b % 3 := by
  have hm := congrArg (fun z : ℤ => z % 3) h
  have ha := Int.emod_nonneg a (by norm_num : (3 : ℤ) ≠ 0)
  have hb := Int.emod_nonneg b (by norm_num : (3 : ℤ) ≠ 0)
  have ha' := Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 3)
  have hb' := Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 3)
  have hn : ¬ (a % 3 = 0 ∧ b % 3 = 0) := by
    rintro ⟨h1, h2⟩
    have hu := hab.isUnit_of_dvd' (Int.dvd_of_emod_eq_zero h1)
      (Int.dvd_of_emod_eq_zero h2)
    norm_num [Int.isUnit_iff_abs_eq] at hu
  interval_cases h1 : a % 3 <;> interval_cases h2 : b % 3 <;>
    norm_num [pow_succ, Int.add_emod, Int.mul_emod, h1, h2] at *

theorem coprime_three {u : ℤ} (hu : u % 3 ≠ 0) : IsCoprime u 3 := by
  have h0 := Int.emod_nonneg u (by norm_num : (3 : ℤ) ≠ 0)
  have h3 := Int.emod_lt_of_pos u (by norm_num : (0 : ℤ) < 3)
  have he := Int.emod_add_mul_ediv u 3
  interval_cases h : u % 3
  · exact (hu rfl).elim
  · refine ⟨1, -(u / 3), ?_⟩
    nlinarith
  · refine ⟨-1, u / 3 + 1, ?_⟩
    nlinarith

theorem tangent_coprime {a b c : ℤ} (h : a ^ 3 + b ^ 3 = 9 * c ^ 3)
    (hab : IsCoprime a b) :
    IsCoprime (a * (a ^ 3 + 2 * b ^ 3)) (-b * (2 * a ^ 3 + b ^ 3)) := by
  have hr := residues h hab
  have hu3 : (a ^ 3 + 2 * b ^ 3) % 3 ≠ 0 := by
    have ha := Int.emod_nonneg a (by norm_num : (3 : ℤ) ≠ 0)
    have hb := Int.emod_nonneg b (by norm_num : (3 : ℤ) ≠ 0)
    have ha' := Int.emod_lt_of_pos a (by norm_num : (0 : ℤ) < 3)
    have hb' := Int.emod_lt_of_pos b (by norm_num : (0 : ℤ) < 3)
    interval_cases h1 : a % 3 <;> interval_cases h2 : b % 3
    all_goals norm_num [pow_succ, Int.add_emod, Int.mul_emod, h1, h2]
    all_goals norm_num at hr
  have hav : IsCoprime a (2 * a ^ 3 + b ^ 3) := by
    convert hab.pow_right (n := 3) |>.mul_add_right_right (2 * a ^ 2) using 1
    ring
  have hub : IsCoprime (a ^ 3 + 2 * b ^ 3) b := by
    convert hab.pow_left (m := 3) |>.add_mul_right_left (2 * b ^ 2) using 1
    ring
  have huv : IsCoprime (a ^ 3 + 2 * b ^ 3) (2 * a ^ 3 + b ^ 3) := by
    have hh := (coprime_three hu3).mul_right (hub.pow_right (n := 3))
    convert hh.neg_right.add_mul_right_right 2 using 1
    ring
  exact (hab.neg_right.mul_right hav).mul_left (hub.neg_right.mul_right huv)

theorem tangent_equation {a b c : ℤ} (h : a ^ 3 + b ^ 3 = 9 * c ^ 3) :
    (a * (a ^ 3 + 2 * b ^ 3)) ^ 3 + (-b * (2 * a ^ 3 + b ^ 3)) ^ 3 =
      9 * (c * (a ^ 3 - b ^ 3)) ^ 3 := by
  linear_combination (a ^ 3 - b ^ 3) ^ 3 * h

theorem cube_gap {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    2 ≤ |a ^ 3 - b ^ 3| := by
  have ho : Odd (3 : ℕ) := by decide
  wlog hlt : a < b generalizing a b
  · have he := this hb ha hab.symm (by omega)
    simpa only [abs_sub_comm] using he
  rw [abs_of_nonpos (sub_nonpos.mpr (ho.strictMono_pow.monotone hlt.le))]
  by_cases ha0 : 0 < a
  · have hs : (a + 1) ^ 3 ≤ b ^ 3 := ho.strictMono_pow.monotone (by omega)
    nlinarith [sq_nonneg a]
  · by_cases hb0 : 0 < b
    · have h1 : a ^ 3 ≤ (-1 : ℤ) ^ 3 := ho.strictMono_pow.monotone (by omega)
      have h2 : (1 : ℤ) ^ 3 ≤ b ^ 3 := ho.strictMono_pow.monotone (by omega)
      norm_num at h1 h2
      omega
    · have hs : (a + 1) ^ 3 ≤ b ^ 3 := ho.strictMono_pow.monotone (by omega)
      have ha2 : a ≤ -2 := by omega
      nlinarith [sq_nonneg (a + 1)]

theorem denominator_growth {a b c : ℤ} (h : a ^ 3 + b ^ 3 = 9 * c ^ 3)
    (hab : IsCoprime a b) (hc : c ≠ 0) :
    c.natAbs < (c * (a ^ 3 - b ^ 3)).natAbs := by
  have hr := residues h hab
  have ha : a ≠ 0 := by intro ha; simp [ha] at hr
  have hb : b ≠ 0 := by intro hb; simp [hb] at hr
  have hab' : a ≠ b := by intro he; exact hr.2.2 (congrArg (fun z : ℤ => z % 3) he)
  have hd : 2 ≤ (a ^ 3 - b ^ 3).natAbs := by
    have hh := cube_gap ha hb hab'
    rw [← Int.natCast_natAbs] at hh
    exact_mod_cast hh
  rw [Int.natAbs_mul]
  have hc' : 0 < c.natAbs := Int.natAbs_pos.mpr hc
  nlinarith

def triple : ℕ → ℤ × ℤ × ℤ
  | 0 => (1, 2, 1)
  | n + 1 =>
      let t := triple n
      (t.1 * (t.1 ^ 3 + 2 * t.2.1 ^ 3),
        -t.2.1 * (2 * t.1 ^ 3 + t.2.1 ^ 3),
        t.2.2 * (t.1 ^ 3 - t.2.1 ^ 3))

theorem triple_invariants (n : ℕ) :
    (triple n).1 ^ 3 + (triple n).2.1 ^ 3 = 9 * (triple n).2.2 ^ 3 ∧
      IsCoprime (triple n).1 (triple n).2.1 ∧ (triple n).2.2 ≠ 0 := by
  induction n with
  | zero => norm_num [triple, isCoprime_one_left]
  | succ n ih =>
      have hg := denominator_growth ih.1 ih.2.1 ih.2.2
      exact ⟨tangent_equation ih.1, tangent_coprime ih.1 ih.2.1,
        Int.natAbs_pos.mp (lt_of_le_of_lt (Nat.zero_le _) hg)⟩

theorem height_strictMono : StrictMono (fun n => (triple n).2.2.natAbs) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact denominator_growth (triple_invariants n).1
    (triple_invariants n).2.1 (triple_invariants n).2.2

def point (n : ℕ) : ℚ × ℚ :=
  ((triple n).1 / (triple n).2.2, (triple n).2.1 / (triple n).2.2)

theorem point_equation (n : ℕ) : (point n).1 ^ 3 + (point n).2 ^ 3 = 9 := by
  have h := triple_invariants n
  have hc : ((triple n).2.2 : ℚ) ≠ 0 := by exact_mod_cast h.2.2
  have he : ((triple n).1 : ℚ) ^ 3 + ((triple n).2.1 : ℚ) ^ 3 =
      9 * ((triple n).2.2 : ℚ) ^ 3 := by exact_mod_cast h.1
  dsimp [point]
  field_simp
  simpa only [mul_comm] using he

theorem common_denominator_dvd {a b c u v d : ℤ} (hab : IsCoprime a b)
    (hc : c ≠ 0) (hd : d ≠ 0)
    (ha : (a : ℚ) / c = (u : ℚ) / d)
    (hb : (b : ℚ) / c = (v : ℚ) / d) : c ∣ d := by
  have hcq : (c : ℚ) ≠ 0 := by exact_mod_cast hc
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have h1 : a * d = u * c := by exact_mod_cast (div_eq_div_iff hcq hdq).mp ha
  have h2 : b * d = v * c := by exact_mod_cast (div_eq_div_iff hcq hdq).mp hb
  obtain ⟨r, s, hrs⟩ := hab
  refine ⟨r * u + s * v, ?_⟩
  linear_combination -d * hrs + r * h1 + s * h2

theorem point_injective : Function.Injective point := by
  intro n m hnm
  have hn := triple_invariants n
  have hm := triple_invariants m
  have h1 := congrArg Prod.fst hnm
  have h2 := congrArg Prod.snd hnm
  have hnm' := common_denominator_dvd hn.2.1 hn.2.2 hm.2.2 h1 h2
  have hmn' := common_denominator_dvd hm.2.1 hm.2.2 hn.2.2 h1.symm h2.symm
  apply height_strictMono.injective
  exact Nat.dvd_antisymm (Int.natAbs_dvd_natAbs.mpr hnm')
    (Int.natAbs_dvd_natAbs.mpr hmn')

theorem infinitely_many : Set.Infinite {p : ℚ × ℚ | p.1 ^ 3 + p.2 ^ 3 = 9} := by
  apply (Set.infinite_range_of_injective point_injective).mono
  rintro p ⟨n, rfl⟩
  exact point_equation n

end RationalCubicNineInfinitude

theorem solution : ∀ _n : ℕ, ∃ x y : ℚ, x ^ 3 + y ^ 3 = 9 := by
  intro n
  exact ⟨(RationalCubicNineInfinitude.point n).1, (RationalCubicNineInfinitude.point n).2,
    RationalCubicNineInfinitude.point_equation n⟩

#print axioms RationalCubicNineInfinitude.residues
#print axioms RationalCubicNineInfinitude.coprime_three
#print axioms RationalCubicNineInfinitude.tangent_coprime
#print axioms RationalCubicNineInfinitude.tangent_equation
#print axioms RationalCubicNineInfinitude.cube_gap
#print axioms RationalCubicNineInfinitude.denominator_growth
#print axioms RationalCubicNineInfinitude.triple
#print axioms RationalCubicNineInfinitude.triple_invariants
#print axioms RationalCubicNineInfinitude.height_strictMono
#print axioms RationalCubicNineInfinitude.point
#print axioms RationalCubicNineInfinitude.point_equation
#print axioms RationalCubicNineInfinitude.common_denominator_dvd
#print axioms RationalCubicNineInfinitude.point_injective
#print axioms RationalCubicNineInfinitude.infinitely_many
#print axioms solution
