-- Prove2me | Theorems.Thm_mme_CW_q6_primary_profile_capacity_quarter_root
-- name    : mme_CW_q6_primary_profile_capacity_quarter_root
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T16:35:06.998867+00:00
-- url     : https://prove2.me/theorems/3415136c-f476-48d2-8e1a-3d04a2fa1cff
-- title:
--   Coupled q=6 multinomial capacity attains the raw profile below a fourth-root loss
-- statement:
--   Fix \(\tau\) with \(3\tau\ge2\), and for the coupled \(q=6\) profile set
--   \[
--   L=\left\lfloor\frac{2N}{6^{3\tau}+2}\right\rfloor,\quad
--   G=N-L,\quad s=36^{2G}6^{2L},\quad
--   R=4\,6^{3\tau}(6^{3\tau}+2).
--   \]
--   Let
--   \[
--   Z=\binom{2N}{L}\binom{2N-L}{L},\qquad
--   X=\binom NG,\qquad B=\binom{2G}{G},\qquad
--   \mathcal C_{N,L,G}=\frac{Z^3B^2}{16X^4}.
--   \]
--   Whenever the profile conditions \(L>0\), \(L+G=N\), and \(341L<100G\) hold, then for all sufficiently large \(N\),
--   \[
--   \bigl(R e^{-\delta_N/2}\bigr)^{2N}
--   \le
--   \mathcal C_{N,L,G}e^{-N\delta_N/2}(s^3)^\tau,
--   \qquad \delta_N=(N+1)^{-1/4}.
--   \]
--
--   This is the analytic half of the primary C-tensor estimate.  It formalizes the multinomial/Stirling calculation and the optimized \(L/G\) profile on journal pp. 271--272, with the fourth-root discount absorbing floor, polynomial, and fixed-constant errors.  It contains no tensor-support or hashing assertion.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), the auxiliary equation and optimized profile on journal pp. 271--272; https://www.sciencedirect.com/science/article/pii/S0747717108800132

import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
open Filter Topology

theorem mme_CW_q6_primary_profile_capacity_quarter_root
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let side : ℕ := 36 ^ (2 * Gcount) * 6 ^ (2 * L)
      let raw : ℝ :=
        4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)
      let Zcount : ℕ :=
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      let Xcount : ℕ := Nat.choose N Gcount
      let middle : ℕ := Nat.choose (2 * Gcount) Gcount
      let capacity : ℝ :=
        ((Zcount : ℝ) ^ 3 * (middle : ℝ) ^ 2) /
          (16 * (Xcount : ℝ) ^ 4)
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
        (raw * Real.exp (-(loss / 2))) ^ (2 * N) ≤
          (capacity * Real.exp (-((N : ℝ) * loss / 2))) *
            ((((side * side * side : ℕ) : ℝ)) ^ tau) := by sorry
