-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_induced_family_exists
-- name    : mme_CW_q6_primary_hash_induced_family_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T17:55:54.977159+00:00
-- url     : https://prove2.me/theorems/ae38998b-49ad-48d8-bb32-cd19b821bd52
-- title:
--   Finite Salem--Spencer C-tensor fiber family with q=6 outer and middle counts
-- statement:
--   Fix \(\tau\) with \(3\tau\ge2\), and set \(L=\lfloor 2N/(6^{3\tau}+2)\rfloor\) and \(G=N-L\). Let
--   \[
--   Z=\binom{2N}{L}\binom{2N-L}{L},\qquad
--   X=\binom NG,\qquad
--   B=\binom{2G}{G},\qquad
--   \delta_N=(N+1)^{-1/4}.
--   \]
--   Whenever \(L>0\), \(L+G=N\), and \(341L<100G\), for all sufficiently large \(N\) there are integers \(A,H\) and an induced primary hash family with \(A\) outer mode-two fibers of common positive size \(H\). The family has globally distinct mode-zero and mode-one words, distinct mode-two words between fibers, and no unintended supported mixed address. It satisfies
--   \[
--   H\le4^N,\qquad
--   Z e^{-N\delta_N/12}\le A,\qquad
--   B e^{-N\delta_N/8}\le4X^2H.
--   \]
--
--   This is the field-independent finite combinatorial output of the first Salem--Spencer hash and collision-pruning stage on CW90 journal p. 271. The explicit fourth-root slack absorbs Behrend density and equal-fiber losses. The conclusion is an incidence family only; tensor realization is a separate theorem.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--271: exact X/Y/Z type counts, M=4*binom(N,G)^2+1, Salem--Spencer hashing, collision deletion, and equal-size C-tensor fibers; https://www.sciencedirect.com/science/article/pii/S0747717108800132. The finite density input is mme_behrend_explicit_threeAP_free (Prove2Me cb45e6ba-b86a-4119-a08e-f162c8fbc86b).

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_mme_CW_q6_primary_hash_family
import Theorems.Thm_mme_behrend_explicit_threeAP_free
import Theorems.Thm_mme_3AP_free_no_collision
open MME Filter Topology

theorem mme_CW_q6_primary_hash_induced_family_exists
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let Zcount : ℕ :=
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      let Xcount : ℕ := Nat.choose N Gcount
      let middle : ℕ := Nat.choose (2 * Gcount) Gcount
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∃ A H : ℕ, ∃ family : CWQ6PrimaryHashFamily N L Gcount A H,
        H ≤ 4 ^ N ∧
        (Zcount : ℝ) * Real.exp (-((N : ℝ) * loss / 12)) ≤
          (A : ℝ) ∧
        (middle : ℝ) * Real.exp (-((N : ℝ) * loss / 8)) ≤
          4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by sorry
