-- Prove2me | solution 1 for lean_workbook_plus_44405
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:01:01.536786+00:00
-- url     : https://prove2.me/submissions/68922727-733e-4724-aa7d-e600b88d6673

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Tactic.Ring

theorem prime_residue_unique (a x y p : ℤ) (hp : Prime p) (hpa : ¬ p ∣ a)
    (h0 : 0 < x ∧ 0 < y) (hxp : x ≤ p) (hyp : y ≤ p)
    (h : x * a ≡ y * a [ZMOD p]) : x = y := by
  have hd : p ∣ (y - x) * a := by
    convert h.dvd using 1 <;> ring
  have hxy : x ≡ y [ZMOD p] := by
    apply Int.modEq_of_dvd
    exact (hp.dvd_or_dvd hd).resolve_right hpa
  have hm : (x - 1) % p = (y - 1) % p := hxy.sub_right 1
  rw [Int.emod_eq_of_lt (by omega) (by omega),
    Int.emod_eq_of_lt (by omega) (by omega)] at hm
  omega

theorem solution (a x y p : ℤ) (hp : Prime p) (hpa : ¬ p ∣ a)
    (h0 : 0 < x ∧ 0 < y) (hxp : x ≤ p) (hyp : y ≤ p)
    (h : x * a ≡ y * a [ZMOD p]) : x ≡ y [ZMOD p] := by
  rw [prime_residue_unique a x y p hp hpa h0 hxp hyp h]

#print axioms solution
