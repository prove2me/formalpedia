-- Prove2me | Theorems.Thm_flt5_zz5_unit_norm_one
-- name    : flt5_zz5_unit_norm_one
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-13T09:35:11.000202+00:00
-- url     : https://prove2.me/theorems/21a574f6-d227-4d66-9c32-089bb089b854
-- statement:
--   Every unit u of ZZ5 = Z[ζ₅] has Algebra.norm ℤ u = 1. Proof: units satisfy u*u⁻¹=1, so N(u)*N(u⁻¹)=N(1)=1, hence N(u)∈{1,-1}. For ZZ5, units are {±ζ^k: k=0,...,4}. N(ζ^k)=ζ^(10k)=1 and N(-1)=(-1)^4=1 (degree 4 extension), so N(u)=1 for all units u.

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Data.Int.Basic

theorem flt5_zz5_unit_norm_one (u : (NumberField.RingOfIntegers (CyclotomicField 5 ℚ))ˣ) : Algebra.norm ℤ (u : NumberField.RingOfIntegers (CyclotomicField 5 ℚ)) = 1 := by sorry
