-- Prove2me | solution 1 for mme_released_interior_owner2_cell33_region4_112_weight_rate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-24T16:38:54.241719+00:00
-- url     : https://prove2.me/submissions/1dbf85ca-aa91-4be8-9ac5-b34eb2af55dc

import Theorems.Thm_mme_rational_112_weight_rate_certificate
import Theorems.Thm_mme_rational_log_series_certificate
import Definitions.Def_mme_released_interior_integer_profiles

open scoped BigOperators
open MME MME.RegionRate MME.MoreAsymmetryExactSeed

private def parameter (z : Fin 3) : ℕ := ![994710286, 20992808152, 0] z

private def boundNumerator (z : Fin 3) : ℕ := ![36109961865559, 36249639233961, 36077370863541] z

private def logScale (z a : Fin 3) : ℕ :=
  (![![10, 10, 1], ![6, 6, 1], ![0, 0, 0]] : Fin 3 → Fin 3 → ℕ) z a

private def lowerMagnitude (z a : Fin 3) : ℕ :=
  (![![6913059033054, 6913059033054, 1991402098], ![3863575368867, 3863575368867, 42892486828], ![0, 0, 0]] : Fin 3 → Fin 3 → ℕ) z a

private def upperMagnitude (z a : Fin 3) : ℕ :=
  (![![6913059033053, 6913059033053, 1991402097], ![3863575368866, 3863575368866, 42892486827], ![0, 0, 0]] : Fin 3 → Fin 3 → ℕ) z a

private def p (z : Fin 3) : ℚ := (parameter z : ℚ) / 1000000000000

private def lower (z a : Fin 3) : ℚ := -(lowerMagnitude z a : ℚ) / 1000000000000
private def upper (z a : Fin 3) : ℚ := -(upperMagnitude z a : ℚ) / 1000000000000
private def bound (z : Fin 3) : ℚ := (boundNumerator z : ℚ) / 1000000000000

private theorem log_bounds (z a : Fin 3)
    (hp : 0 < (![p z, p z, 1 - 2 * p z] : Fin 3 → ℚ) a) :
    (lower z a : ℝ) ≤ Real.log (((![p z, p z, 1 - 2 * p z] : Fin 3 → ℚ) a : ℚ) : ℝ) ∧
      Real.log (((![p z, p z, 1 - 2 * p z] : Fin 3 → ℚ) a : ℚ) : ℝ) ≤ (upper z a : ℝ) := by
  apply mme_rational_log_series_certificate _ hp (logScale z a) 16
  all_goals revert z a; decide +kernel

/-- The complete entropy and dimension rate of an actual released 112 child
has a rational lower bound for each location of its grade two coordinate. -/
theorem solution
    (c : ReleasedInterior.Split 33) (z : Fin 3)
    (hshape : ∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) :
    let q : ℝ := ((((((ReleasedInterior.seed 2 33).children.find?
      (fun a => a.1 == 4 && a.2.1 == ReleasedInterior.sourceShape 2 c)).getD
        (0, [], 0)).2.2)) : ℝ) / denominator
    (((![36109961865559, 36249639233961, 36077370863541] : Fin 3 → ℕ) z : ℝ) / 1000000000000) ≤
      4 * (entropy ![q, q, 1 - 2 * q] + 2 * Real.log 2) +
        24 * (1 - q) * (3952233 / 5000000 : ℝ) * Real.log 5 := by
  intro q
  have hid : ∀ (c : ReleasedInterior.Split 33) (z : Fin 3),
      (∀ i : Fin 3, (c.val i).val = if i = z then 2 else 1) →
        (((((ReleasedInterior.seed 2 33).children.find?
      (fun a => a.1 == 4 && a.2.1 == ReleasedInterior.sourceShape 2 c)).getD
        (0, [], 0)).2.2)) = parameter z := by decide +kernel
  have hq : q = (parameter z : ℝ) / denominator := by
    dsimp [q]
    rw [hid c z hshape]
  rw [hq]
  have hp : ∀ z, 0 ≤ p z := by decide +kernel
  have hpmax : ∀ z, p z ≤ 1 / 2 := by decide +kernel
  have h := mme_rational_112_weight_rate_certificate (p z) (3952233 / 5000000)
    (hp z) (hpmax z) (by norm_num) (lower z) (upper z) (log_bounds z) (bound z) ?_
  · simpa only [p, bound, boundNumerator, denominator, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one, Rat.cast_zero] using h
  · clear hq hshape hid q c
    revert z; decide +kernel


#print axioms solution
