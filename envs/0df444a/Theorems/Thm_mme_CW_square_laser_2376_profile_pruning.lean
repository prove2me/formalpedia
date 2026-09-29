-- Prove2me | Theorems.Thm_mme_CW_square_laser_2376_profile_pruning
-- name    : mme_CW_square_laser_2376_profile_pruning
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-24T05:02:29.769865+00:00
-- url     : https://prove2.me/theorems/23a3c4da-6026-4d6e-a0d2-2f976efd5a8a
-- title:
--   Finite CW square laser extraction at the exact 2.376 profile
-- statement:
--   Fix $q=6$, $3\tau\ge2$, and the exact rational joint profile of the Coppersmith--Winograd $2.376$ certificate. There is a profile-pruning loss $\eta_m\in[0,1]$ with $\eta_m\to0$ having the following property. Suppose a concrete matrix-multiplication direct sum restricts from the $m$-th power of the cyclic symmetrization of the coupled $(1,1,2)$ constituent and has tau-weight at least
--
--   $$
--   \left(2^{2/3}6^\tau(6^{3\tau}+2)^{1/3}\right)^{3m}(1-\delta),
--   \qquad 0<\delta\le1.
--   $$
--
--   Then a concrete direct sum restricts from $T_6^{\otimes 6{,}000{,}000m}$ and has tau-weight at least
--
--   $$
--   \operatorname{auxiliaryRHS}(6,\tau,a,b,c,d)^{3{,}000{,}000m}
--   \left(1-\eta_m-\left[1-(1-\delta)^{616627}\right]\right),
--   $$
--
--   where $(a,b,c,d)=(699,37518,307638,616627)/3{,}000{,}000$. The exponent $616627$ is exact: at this profile the three cyclic coupled classes each occur $616627m$ times, so the supplied cyclic coupled witness is Kronecker-powered that many times. The loss $\eta_m$ is the remaining subexponential loss from five-grade type selection, Salem--Spencer hashing, and collision elimination. Both hypotheses and conclusion retain actual finite tensor restrictions, rather than only their entropy or value surrogates.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), tensor-square type selection, equations (11)--(13), Salem--Spencer pruning, and auxiliary bound on journal pp. 265--269 (PDF pp. 15--19); https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Definitions.Def_mme_CW_auxiliary_RHS
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_CW_tensor
open MME BigOperators Filter
universe u

theorem mme_CW_square_laser_2376_profile_pruning
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ laserError : ℕ → ℝ,
      Tendsto laserError atTop (nhds 0) ∧
      (∀ m, 0 ≤ laserError m ∧ laserError m ≤ 1) ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ (delta : ℝ), 0 < delta → delta ≤ 1 →
        ∀ (kc : ℕ) (xc yc zc : Fin kc → ℕ),
          TensorObj.Restrict
              (TensorObj.bigAdd (fun i => MMObj K (xc i) (yc i) (zc i)))
              ((cyclicSymmetrization (coupledObj K 6)).kronPow m) →
          (((2 : ℝ) ^ ((2 : ℝ) / 3) *
                (6 : ℝ) ^ tau *
                (((6 : ℝ) ^ (3 * tau) + 2) ^ ((1 : ℝ) / 3))) ^ (3 : ℕ)) ^ m *
              (1 - delta) ≤
            ∑ i, (((xc i * yc i * zc i : ℕ) : ℝ) ^ tau) →
          ∃ (k : ℕ) (x y z : Fin k → ℕ),
            TensorObj.Restrict
                (TensorObj.bigAdd (fun i => MMObj K (x i) (y i) (z i)))
                ((CWObj K 6).kronPow (6000000 * m)) ∧
            (auxiliaryRHS 6 tau
                cw2376_a cw2376_b cw2376_c cw2376_d) ^ (3000000 * m) *
                (1 -
                  (laserError m +
                    (1 - (1 - delta) ^ (616627 : ℕ)))) ≤
              ∑ i, (((x i * y i * z i : ℕ) : ℝ) ^ tau) := by sorry
