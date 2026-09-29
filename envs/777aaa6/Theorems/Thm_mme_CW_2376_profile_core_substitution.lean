-- Prove2me | Theorems.Thm_mme_CW_2376_profile_core_substitution
-- name    : mme_CW_2376_profile_core_substitution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T15:55:50.240106+00:00
-- url     : https://prove2.me/theorems/4fd61dc3-e249-4fae-b48b-860c2d7d7428
-- title:
--   Substitute a finite coupled witness into all exact-profile cores
-- statement:
--   Fix $3\tau\ge2$, a nonnegative coupled base $V_c$, a scale $m$, and $s$ surviving profile cores. A concrete witness of weight at least $V_c^m(1-\delta)$ for the $m$-th cyclic-coupled power can be Kronecker-powered exactly $616627$ times and substituted into every core. The resulting concrete matrix-multiplication direct sum restricts from the $s$ cores and has tau-weight at least $$s P(\tau,V_c)^{3{,}000{,}000m}(1-\delta)^{616627}.$$ This retains both the literal finite restriction and the exact error amplification.
-- source:
--   Coppersmith--Winograd (1990), tensor-square constituents (b)--(d) on journal p. 266, equation (13) on p. 268, auxiliary product on p. 269, and cyclic coupled lemma on pp. 270--272.

import Definitions.Def_mme_CW_2376_profile_data
open MME BigOperators
universe u

theorem mme_CW_2376_profile_core_substitution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (Vc : ℝ) (hVc_nonneg : 0 ≤ Vc)
    (m s : ℕ)
    (delta : ℝ) (hdelta_pos : 0 < delta) (hdelta_lt : delta < 1)
    (kc : ℕ) (xc yc zc : Fin kc → ℕ)
    (hc_restrict :
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (xc i) (yc i) (zc i)))
        ((cyclicSymmetrization (coupledObj K 6)).kronPow m))
    (hc_weight :
      Vc ^ m * (1 - delta) ≤
        ∑ i, (((xc i * yc i * zc i : ℕ) : ℝ) ^ tau)) :
    ∃ (k : ℕ) (x y z : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i => MMObj K (x i) (y i) (z i)))
        (TensorObj.bigAdd
          (fun _ : Fin s => cw2376ProfileCore K m)) ∧
      (s : ℝ) *
          (cw2376ProfileNumeratorBase tau Vc ^ (3000000 * m)) *
          (1 - delta) ^ (616627 : ℕ) ≤
        ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by
  sorry
