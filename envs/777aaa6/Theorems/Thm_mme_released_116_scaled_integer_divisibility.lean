-- Prove2me | Theorems.Thm_mme_released_116_scaled_integer_divisibility
-- name    : mme_released_116_scaled_integer_divisibility
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T13:33:25.05178+00:00
-- url     : https://prove2.me/theorems/b16a5f01-a856-4ebb-af39-4818fbb615ab
-- title:
--   Replication preserves the released extraction divisor and size lower bound
-- statement:
--   For every positive integer $k$, the released owner-zero $(1,1,6)$ data satisfy
--   $$0<kd^2,\qquad kd^2\le kn_r,\qquad kd^2\mid km_r(c)$$
--   for all regions and admissible splits, with $d=10^{12}$. The common extraction minimum therefore grows linearly with replication.
-- source:
--   Integer replication of regional profiles and the released owner-zero (1,1,6) component.

import Definitions.Def_mme_released_116_integer_profiles
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic.NormNum

open BigOperators MME MME.Released116 MME.MoreAsymmetryExactSeed
set_option autoImplicit false

theorem mme_released_116_scaled_integer_divisibility (k : ℕ) (hk : 0 < k) :
    0 < k * denominator ^ 2 ∧
      (∀ r : Fin 6, k * denominator ^ 2 ≤ k * regionalSize r) ∧
      ∀ (r : Fin 6) (c : Split), k * denominator ^ 2 ∣ k * splitCount r c := by sorry
