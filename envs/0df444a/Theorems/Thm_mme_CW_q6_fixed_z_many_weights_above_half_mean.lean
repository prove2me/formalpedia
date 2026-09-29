-- Prove2me | Theorems.Thm_mme_CW_q6_fixed_z_many_weights_above_half_mean
-- name    : mme_CW_q6_fixed_z_many_weights_above_half_mean
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:51:14.743346+00:00
-- url     : https://prove2.me/theorems/f5069e7b-1228-432d-ab26-941b0e721dd9
-- title:
--   Many q=6 weights retain at least half the mean of a fixed Z-fiber
-- statement:
--   Fix a common Z-word and a family of exactly $B>0$ exact coupled q=6 addresses above it. For each address, subtract its doubled Z-hash coefficient word from its doubled X-hash coefficient word. Let $D(w)$ count the resulting linear forms that vanish at a weight vector $w\in(\mathbb Z/M\mathbb Z)^{2n+2}$. If $M>2$, the element $2$ is a unit modulo $M$, the middle profile is positive, and $2MH\le B$, then\n\n$$\nB M^{2n+2}\le 4(2M+B)\,|\{w:H\le D(w)\}|.\n$$\n\nThus a source-scale proportion of all weights retain at least any prescribed threshold below half the mean fixed-Z degree. The cross-multiplied form remains meaningful without division and preserves the common Z-fiber multiplicity needed for the q=6 C-tensor construction.
-- source:
--   Finite Paley--Zygmund applied to the fixed-Z dependent-weight calculation in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), pp. 270--271

import Mathlib
import Theorems.Thm_mme_finite_second_moment_many_above_threshold
import Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_first_second_moment

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_CW_q6_fixed_z_many_weights_above_half_mean
    {M n L G B H : ℕ} [NeZero M]
    (hM : 2 < M) (h2 : IsUnit (2 : ZMod M)) (hG : 0 < G)
    (A : Finset (CWQ6ExactCoupledAddress (n + 1) L G))
    (z : Fin (2 * (n + 1)) → Fin 3)
    (hz : ∀ e ∈ A, e.1 2 = z)
    (hcard : A.card = B) (hB : 0 < B)
    (hH : 2 * M * H ≤ B) :
    let c : {e // e ∈ A} → Fin (2 * n + 2) → ZMod M := fun e j =>
      (2 * ((e.1.1 0 j).val : ZMod M)) -
        (cwQ6CoupledZHashCode (e.1.1 2 j) : ZMod M)
    (B : ℝ) * (M : ℝ) ^ (2 * n + 2) ≤
      4 * (2 * (M : ℝ) + (B : ℝ)) *
        (((Finset.univ : Finset (Fin (2 * n + 2) → ZMod M)).filter
          (fun w => H ≤ (A.attach.filter
            (fun e => ∑ i, c e i * w i = 0)).card)).card : ℝ) := by
  sorry
