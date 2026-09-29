-- Prove2me | Definitions.Def_mme_certified_entropy_rational_data
-- name    : mme_certified_entropy_rational_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-22T20:59:41.065462+00:00
-- url     : https://prove2.me/theorems/1344d46a-5025-4dd1-baba-2d452d50b0b4
-- title:
--   Rational data for certified entropy bounds
-- statement:
--   Rational data for certified entropy bounds: the four primes 2, 3, 5, 7 whose logarithms carry every reference value; the rational reference 2^a 3^b 5^c 7^d with its positivity and its cast to the real reference; the expansion of a reference logarithm over the four prime logarithms; and certified 24-digit rational lower and upper bounds for those four logarithms.
-- source:
--   Certified evaluation of the entropy rates of the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6).

import Mathlib
import Definitions.Def_mme_certified_entropy_reference

open BigOperators MME MME.RegionRate MME.Cert
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace MME.Cert

/-- The four primes whose logarithms carry every reference value. -/
def primeOf : Fin 4 → ℕ := ![2, 3, 5, 7]

theorem primeOf_pos (j : Fin 4) : 0 < primeOf j := by
  fin_cases j <;> decide

/-- The rational reference value `2^a 3^b 5^c 7^d`. -/
def qvalQ (e : Fin 4 → ℤ) : ℚ := 2 ^ (e 0) * 3 ^ (e 1) * 5 ^ (e 2) * 7 ^ (e 3)

theorem qvalQ_pos (e : Fin 4 → ℤ) : 0 < qvalQ e := by
  unfold qvalQ
  have h2 : (0 : ℚ) < 2 ^ (e 0) := zpow_pos (by norm_num) _
  have h3 : (0 : ℚ) < 3 ^ (e 1) := zpow_pos (by norm_num) _
  have h5 : (0 : ℚ) < 5 ^ (e 2) := zpow_pos (by norm_num) _
  have h7 : (0 : ℚ) < 7 ^ (e 3) := zpow_pos (by norm_num) _
  positivity

theorem qvalQ_cast (e : Fin 4 → ℤ) : ((qvalQ e : ℚ) : ℝ) = qval e := by
  unfold qvalQ qval
  push_cast
  ring

theorem log_qval_prime (e : Fin 4 → ℤ) :
    Real.log (qval e) = ∑ j, (e j : ℝ) * Real.log (primeOf j) := by
  rw [log_qval e, Fin.sum_univ_four]
  show _ = (e 0 : ℝ) * Real.log ((2 : ℕ) : ℝ) + (e 1 : ℝ) * Real.log ((3 : ℕ) : ℝ) +
    (e 2 : ℝ) * Real.log ((5 : ℕ) : ℝ) + (e 3 : ℝ) * Real.log ((7 : ℕ) : ℝ)
  norm_num

/-- Certified rational lower bounds for the logarithms of 2, 3, 5 and 7. -/
def logLo : Fin 4 → ℚ := ![693147180559945309417232/10^24, 1098612288668109691395245/10^24, 1609437912434100374600759/10^24, 1945910149055313305105352/10^24]

/-- Certified rational upper bounds for the logarithms of 2, 3, 5 and 7. -/
def logHi : Fin 4 → ℚ := ![693147180559945309417233/10^24, 1098612288668109691395246/10^24, 1609437912434100374600760/10^24, 1945910149055313305105353/10^24]

end MME.Cert


