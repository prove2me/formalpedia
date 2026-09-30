-- Prove2me | solution 1 for lean_workbook_plus_2406
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:30:24.600155+00:00
-- url     : https://prove2.me/submissions/2b1d5bd2-878f-43cf-bc84-9f5e10fe46ed

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

namespace SeventhRootTrace

theorem trace_identity {K : Type*} [Field K] (z : K) (hz : z ≠ 0) :
    (z - 1) * z ^ 3 * ((z + z⁻¹) ^ 3 + (z + z⁻¹) ^ 2 - 2 * (z + z⁻¹) - 1) =
      z ^ 7 - 1 := by
  field_simp
  ring

theorem trace_root {K : Type*} [Field K] (z : K) (hz : z ≠ 0)
    (hz1 : z ≠ 1) (hz7 : z ^ 7 = 1) :
    (z + z⁻¹) ^ 3 + (z + z⁻¹) ^ 2 - 2 * (z + z⁻¹) - 1 = 0 := by
  have h := trace_identity z hz
  rw [hz7, sub_self] at h
  exact (mul_eq_zero.mp h).resolve_left (mul_ne_zero (sub_ne_zero.mpr hz1) (pow_ne_zero _ hz))

theorem root_mod_prime (p : ℕ) (hp : p.Prime) (hp1 : (p : ℤ) ≡ 1 [ZMOD 7]) :
    ∃ t : ZMod p, t ^ 3 + t ^ 2 - 2 * t - 1 = 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hd : 7 ∣ p - 1 :=
    (Nat.modEq_iff_dvd' hp.one_le).mp (Int.natCast_modEq_iff.mp hp1).symm
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card (G := (ZMod p)ˣ) 7
    (by simpa only [ZMod.card_units] using hd)
  have hu7 : (u : ZMod p) ^ 7 = 1 := by
    have h := congrArg (fun v : (ZMod p)ˣ => (v : ZMod p)) (hu ▸ pow_orderOf_eq_one u)
    simpa only [Units.val_pow_eq_pow_val, Units.val_one] using h
  have hu1 : (u : ZMod p) ≠ 1 := by
    intro h
    have : u = 1 := Units.ext h
    rw [this, orderOf_one] at hu
    omega
  exact ⟨(u : ZMod p) + (u : ZMod p)⁻¹,
    trace_root _ (Units.ne_zero u) hu1 hu7⟩

theorem arbitrarily_large_positive_witnesses (p : ℕ) (hp : p.Prime)
    (hp1 : (p : ℤ) ≡ 1 [ZMOD 7]) (N : ℕ) :
    ∃ m : ℕ, N < m ∧ (p : ℤ) ∣ (m : ℤ) ^ 3 + (m : ℤ) ^ 2 - 2 * m - 1 := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨t, ht⟩ := root_mod_prime p hp hp1
  let m := t.val + p * (N + 1)
  have hm : N < m := by
    dsimp [m]
    have := hp.two_le
    nlinarith
  refine ⟨m, hm, (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp ?_⟩
  have hc : (m : ZMod p) = t := by
    simp [m]
  push_cast
  rw [hc]
  exact ht

end SeventhRootTrace

theorem solution (p : ℕ) (hp : p.Prime) (hp1 : p ≡ 1 [ZMOD 7]) :
    ∃ m : ℕ, ((7 : ℤ) ∣ (m ^ 3 + m ^ 2 - 2 * m - 1) % p) := by
  obtain ⟨m, _, hm⟩ := SeventhRootTrace.arbitrarily_large_positive_witnesses p hp hp1 0
  exact ⟨m, by rw [Int.emod_eq_zero_of_dvd hm]; exact dvd_zero 7⟩
