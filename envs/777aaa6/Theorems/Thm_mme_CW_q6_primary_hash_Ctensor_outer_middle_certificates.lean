-- Prove2me | Theorems.Thm_mme_CW_q6_primary_hash_Ctensor_outer_middle_certificates
-- name    : mme_CW_q6_primary_hash_Ctensor_outer_middle_certificates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T04:33:21.202188+00:00
-- url     : https://prove2.me/theorems/7ab51ba8-ab92-4b58-94cf-886d15756c10
-- title:
--   Finite q=6 first-hash bounds with source-faithful C-tensor fibers
-- statement:
--   Fix $\tau$ with $3\tau\ge2$ and, for large $N$, put
--
--   $$
--   L=\left\lfloor\frac{2N}{6^{3\tau}+2}\right\rfloor,\qquad G=N-L.
--   $$
--
--   Under the source pruning conditions, the first Salem--Spencer hash produces $A$ disjoint outer fibers of a common positive size $H$.  These fibers form an actual family of C-tensors over $\langle1,H,1\rangle$ inside the $2N$-th power of the coupled $q=6$ constituent, and every component has volume $6^{4G+2L}$.  With $Z=\binom{2N}{L}\binom{2N-L}{L}$, $X=\binom NG$, $B=\binom{2G}{G}$, and $\delta_N=(N+1)^{-1/4}$,
--
--   $$
--   Ze^{-N\delta_N/12}\le A,\qquad Be^{-N\delta_N/8}\le4X^2H.
--   $$
--
--   Unlike a fixed-survivor factorization, the C-tensor certificate permits the matrix-product identification to depend on the retained address while preserving the common volume used by Strassen's value argument.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270--271: exact type counts, Salem--Spencer hashing, disjoint retained Z-fibers, C-tensors over <1,H,1>, and common component volume; https://doi.org/10.1016/S0747-7171(08)80013-2.

import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_CW_coupled_value

open MME Filter Topology

universe u

theorem mme_CW_q6_primary_hash_Ctensor_outer_middle_certificates
    {K : Type u} [Field K]
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
      ∃ A H : ℕ,
        0 < H ∧
        H ≤ 4 ^ N ∧
        Nonempty
          (CTensorOneHOneFamilyCertificate
            ((coupledObj K 6).kronPow (2 * N))
            A H (6 ^ (4 * Gcount + 2 * L))) ∧
        (Zcount : ℝ) * Real.exp (-((N : ℝ) * loss / 12)) ≤
          (A : ℝ) ∧
        (middle : ℝ) * Real.exp (-((N : ℝ) * loss / 8)) ≤
          4 * (Xcount : ℝ) ^ 2 * (H : ℝ) := by
  sorry
