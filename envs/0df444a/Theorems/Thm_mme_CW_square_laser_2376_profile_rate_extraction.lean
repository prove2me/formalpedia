-- Prove2me | Theorems.Thm_mme_CW_square_laser_2376_profile_rate_extraction
-- name    : mme_CW_square_laser_2376_profile_rate_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T05:41:19.06293+00:00
-- url     : https://prove2.me/theorems/dbfe1bad-e91b-489d-b374-c535367ca175
-- title:
--   Per-root-loss finite CW square extraction at the exact 2.376 profile
-- statement:
--   Fix $q=6$, $3\tau\ge2$, a nonnegative cyclic coupled base $V_c$, and the exact rational joint profile used in the Coppersmith--Winograd $2.376$ certificate. There is a nonnegative per-root loss $r_m\to0$ such that, for every sufficiently large integer $m$, every concrete cyclic-coupled witness at power $m$ with relative error $0<\delta<1$ can be assembled into a concrete direct-sum restriction from $T_6^{\otimes 6{,}000{,}000m}$. Its tau-weight obeys
--
--   $$
--   \left(B_{V_c}(6,\tau,a,b,c,d)e^{-r_m}\right)^{3{,}000{,}000m}(1-\delta)^{616627}
--   \le \sum_i (x_i y_i z_i)^\tau.
--   $$
--
--   Here $(a,b,c,d)=(699,37518,307638,616627)/3{,}000{,}000$. The factor $e^{-r_m}$ records precisely an $\exp(-o(m))$ loss per root from multinomial type counting and Salem--Spencer pruning; it does not assert constant-relative attainment of the boundary. The exponent $616627$ is the exact number of synchronized cyclic coupled copies. The conclusion retains the literal finite tensor restriction needed for the tau-value definition.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square type selection, equations (11)--(13), Salem--Spencer pruning, coupled substitution, Stirling losses, and auxiliary bound on journal pp. 265--269 (PDF pp. 15--19); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_CW_auxiliary_RHS_coupled
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_CW_tensor
open MME BigOperators Filter
universe u

theorem mme_CW_square_laser_2376_profile_rate_extraction
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (Vc : ℝ) (hVc_nonneg : 0 ≤ Vc) :
    ∃ rate : ℕ → ℝ,
      Tendsto rate atTop (nhds 0) ∧
      (∀ m, 0 ≤ rate m) ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ (delta : ℝ), 0 < delta → delta < 1 →
        ∀ (kc : ℕ) (xc yc zc : Fin kc → ℕ),
          TensorObj.Restrict
              (TensorObj.bigAdd (fun i => MMObj K (xc i) (yc i) (zc i)))
              ((cyclicSymmetrization (coupledObj K 6)).kronPow m) →
          Vc ^ m * (1 - delta) ≤
            ∑ i, (((xc i * yc i * zc i : ℕ) : ℝ) ^ tau) →
          ∃ (k : ℕ) (x y z : Fin k → ℕ),
            TensorObj.Restrict
                (TensorObj.bigAdd (fun i => MMObj K (x i) (y i) (z i)))
                ((CWObj K 6).kronPow (6000000 * m)) ∧
            (auxiliaryRHSWithCoupled 6 tau
                cw2376_a cw2376_b cw2376_c cw2376_d Vc *
              Real.exp (-(rate m))) ^ (3000000 * m) *
                (1 - delta) ^ (616627 : ℕ) ≤
              ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by sorry
