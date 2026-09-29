-- Prove2me | Theorems.Thm_fltp_fermat_little
-- name    : fltp_fermat_little
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T09:59:50.683025+00:00
-- url     : https://prove2.me/theorems/412f3e62-94da-4479-a90b-b33bd2abc3d1
-- statement:
--   Fermat's Little Theorem: for any prime p and any integer a, p divides a^p - a. Proved by: (1) showing x^p = x in ZMod p via FiniteField.pow_card (ZMod p is a finite field, Fintype.card (ZMod p) = p), then (2) lifting to ℤ via ZMod.intCast_zmod_eq_zero_iff_dvd. This generalizes flt7_fermat_little (which used 'decide' for p=7) to work for all prime p.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_little_theorem

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic

theorem fltp_fermat_little (p : ℕ) [hp : Fact (Nat.Prime p)] (a : ℤ) : (p : ℤ) ∣ a^p - a := by sorry
