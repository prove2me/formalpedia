-- Prove2me | Theorems.Thm_mme_rational_regional_profiles_common_integer_scale
-- name    : mme_rational_regional_profiles_common_integer_scale
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-30T20:01:27.172773+00:00
-- url     : https://prove2.me/theorems/6de83ae3-6a77-47a6-b21e-79cb68fea040
-- title:
--   Exact common integer scale for rational regional profiles
-- statement:
--   Suppose rational regional sizes $N_r$ are strictly positive, rational split counts $M_{r,s}$ and child histograms $U_{i,s,w}$ are nonnegative, and the exact rational mass constraints hold:
--
--   $$\sum_s M_{r,s}=N_r,\qquad \sum_w U_{i,s,w}=M_{r,s}+M_{r,\bar s}.$$
--
--   There is one positive integer $D$ and natural-number families $n,m,\mu$ satisfying
--
--   $$n_r=D N_r,\qquad m_{r,s}=D M_{r,s},\qquad \mu_{i,s,w}=D U_{i,s,w}$$
--
--   as exact rational equalities. Every $n_r$ is positive. For every positive integer $k$, the replicated counts $k^2n,k^2m,k^2\mu$ remain positive in the regional sizes and satisfy both mass equations exactly.
--
--   The same denominator is used across all regions, modes, split types, and child words, including zero entries. There is no rounding. This auxiliary result provides integer seeds for recursive extraction. Parent-mixture identities, joint support, and rate inequalities must still be established separately.
-- source:
--   Auxiliary exact rational-to-integer conversion for the regional profiles defined at https://prove2.me/theorems/5d673b53-781e-4970-a100-af61d306eba4. Application context: rational verification in Dupont et al., Improving the matrix multiplication exponent with modern optimization and AlphaEvolve, Section 4, https://arxiv.org/html/2608.16884v1#S4. The common-denominator construction and this Lean statement are derived here, not quoted from that paper.

import Definitions.Def_mme_recursive_region_parent_profiles
import Mathlib

open BigOperators MME MME.RecursiveYZ MME.RegionRealization
set_option autoImplicit false

theorem mme_rational_regional_profiles_common_integer_scale
    {half R : ℕ} {W : Type*} [Fintype W]
    (parent : Fin R → Fin 3 → ℕ)
    (htotal : ∀ r, parent r 0 + parent r 1 + parent r 2 = 2 * half)
    (N : Fin R → ℚ) (hN : ∀ r, 0 < N r)
    (M : ∀ r, RecursiveThinSplit.Split half (parent r) → ℚ) (hM : ∀ r s, 0 ≤ M r s)
    (U : Fin 3 → Cell half R parent → W → ℚ) (hU : ∀ i s w, 0 ≤ U i s w)
    (hm : ∀ r, ∑ s, M r s = N r)
    (hu : ∀ i s, ∑ w, U i s w = M s.1 s.2 + M s.1 (complement (htotal s.1) s.2)) :
    ∃ D : ℕ, 0 < D ∧ ∃ n : Fin R → ℕ,
      ∃ m : ∀ r, RecursiveThinSplit.Split half (parent r) → ℕ,
      ∃ mu : Fin 3 → Cell half R parent → W → ℕ,
      (∀ r, (n r : ℚ) = D * N r) ∧
      (∀ r s, (m r s : ℚ) = D * M r s) ∧
      (∀ i s w, (mu i s w : ℚ) = D * U i s w) ∧
      (∀ r, 0 < n r) ∧
      ∀ k : ℕ, 0 < k →
        (∀ r, 0 < k ^ 2 * n r) ∧
        (∀ r, ∑ s, k ^ 2 * m r s = k ^ 2 * n r) ∧
        (∀ i s, ∑ w, k ^ 2 * mu i s w =
          k ^ 2 * m s.1 s.2 + k ^ 2 * m s.1 (complement (htotal s.1) s.2)) := by sorry
