-- Prove2me | Theorems.Thm_mme_CW_q6_fixed_z_difference_hash_first_second_moment
-- name    : mme_CW_q6_fixed_z_difference_hash_first_second_moment
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:36:07.431039+00:00
-- url     : https://prove2.me/theorems/3a1c0d98-cedf-4dcb-88d8-9305d842e6e3
-- title:
--   Exact q=6 fixed-Z first moment and dependent-pair second-moment bound
-- statement:
--   Fix a common Z-word and a finite family $A$ of exact coupled q=6 addresses of tensor-power length $2(n+1)$. For each address let $c_e$ be its doubled X-minus-Z hash coefficient word, and let $D(w)$ count the addresses whose difference equation vanishes at the weight vector $w$. If $M>2$, $2$ is a unit modulo $M$, and $G>0$, then
--
--   $$
--   \sum_w D(w)=|A|M^{2n+1},
--   $$
--
--   and
--
--   $$
--   \sum_wD(w)^2\le2|A|M^{2n+1}+|A|^2M^{2n}.
--   $$
--
--   Equivalently, for uniform $w$, the mean degree is $|A|/M$ and the second moment is at most $2|A|/M+|A|^2/M^2$. The larger term comes from at most two equal-or-opposite code partners per address; every other pair is jointly uniform. This keeps the shared Z-fiber intact and supplies the source-scale concentration input for the q=6 first hash.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), q=6 first-hash dependent-weight calculation on journal pp. 270--271

import Theorems.Thm_mme_finite_injective_linear_code_first_second_moment
import Theorems.Thm_mme_CW_q6_difference_code_has_unit_coefficient
import Theorems.Thm_mme_CW_q6_fixed_z_difference_code_injective
import Theorems.Thm_mme_CW_q6_fixed_z_nondependent_pair_unit_minor

open BigOperators MME

set_option autoImplicit false

theorem mme_CW_q6_fixed_z_difference_hash_first_second_moment
    {M n L G : ℕ} [NeZero M]
    (hM : 2 < M) (h2 : IsUnit (2 : ZMod M)) (hG : 0 < G)
    (A : Finset (CWQ6ExactCoupledAddress (n + 1) L G))
    (z : Fin (2 * (n + 1)) → Fin 3)
    (hz : ∀ e ∈ A, e.1 2 = z) :
    let c : {e // e ∈ A} → Fin (2 * n + 2) → ZMod M := fun e j =>
      (2 * ((e.1.1 0 j).val : ZMod M)) -
        (cwQ6CoupledZHashCode (e.1.1 2 j) : ZMod M)
    (∑ w : Fin (2 * n + 2) → ZMod M,
        (A.attach.filter (fun e => ∑ i, c e i * w i = 0)).card) =
          A.card * M ^ (2 * n + 1) ∧
    (∑ w : Fin (2 * n + 2) → ZMod M,
        (A.attach.filter (fun e => ∑ i, c e i * w i = 0)).card ^ 2) ≤
          2 * A.card * M ^ (2 * n + 1) + A.card ^ 2 * M ^ (2 * n) := by
  sorry
