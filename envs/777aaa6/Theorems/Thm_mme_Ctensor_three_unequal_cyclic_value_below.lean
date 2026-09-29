-- Prove2me | Theorems.Thm_mme_Ctensor_three_unequal_cyclic_value_below
-- name    : mme_Ctensor_three_unequal_cyclic_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T00:43:54.075477+00:00
-- url     : https://prove2.me/theorems/4c5b6eae-f032-49b9-9b1a-d48d1b3904d7
-- title:
--   Unequal cyclic C-tensors attain every strict value below the minimum pair capacity
-- statement:
--   Let $X,Y,Z$ have actual C-tensor certificates with independent positive alphabet sizes $H_0,H_1,H_2$ and positive constant matrix-multiplication component volumes $v_0,v_1,v_2$. Set
--   $$
--   \mu=\min(H_0H_1,H_0H_2,H_1H_2),\qquad v=v_0v_1v_2.
--   $$
--   For every real $\tau$ and every $V$ satisfying $0\le V<\mu v^\tau$, the literal cyclic product has asymptotic $\tau$-value at least $V$:
--   $$
--   V_\tau\bigl(X\otimes\operatorname{cyc}(Y)\otimes\operatorname{cyc}^2(Z)\bigr)\ge V.
--   $$
--
--   The value is witnessed by actual finite direct sums of matrix-multiplication tensors extracted from arbitrarily large powers. No lower bound on $\tau$, equal alphabet sizes, common component shape, or balanced word distribution is assumed. The minimum is taken after the three tensor factors have been combined. The result supplies all strict sub-bounds, not an assertion that the endpoint $\mu v^\tau$ is attained.
-- source:
--   Derived finite-to-asymptotic interface for the cyclic C-tensor laser extraction underlying Coppersmith and Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation9(1990), journal pp271–272, https://doi.org/10.1016/S0747-7171(08)80013-2. It consumes the exact unequal all-words minimum-pair extraction theorem mme_Ctensor_three_unequal_all_words_min_pair_extraction, whose actual source is (threeStarCyclicProduct X Y Z)^R and whose cardinality loss is exp(-100 sqrt(log(min_i H_i^R+1)))/2. The new theorem generalizes the existing equal-star strict-below value proof using independent component volumes and actual unequal word lists. It is an explicitly derived formal adapter, not asserted to be a separately numbered theorem in the source paper; no optimizer certificate or modern exponent is assumed.

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_threeStarCyclicProduct
import Definitions.Def_mme_tau_value

open MME

universe u

set_option autoImplicit false

theorem mme_Ctensor_three_unequal_cyclic_value_below
    {K : Type u} [Field K] {X Y Z : TensorObj K 3}
    {H0 H1 H2 v0 v1 v2 : ℕ}
    (certX : CTensorOneHOneCertificate X H0 v0)
    (certY : CTensorOneHOneCertificate Y H1 v1)
    (certZ : CTensorOneHOneCertificate Z H2 v2)
    (h0 : 0 < H0) (h1 : 0 < H1) (h2 : 0 < H2)
    (hv0 : 0 < v0) (hv1 : 0 < v1) (hv2 : 0 < v2)
    (tau V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < ((min (H0 * H1) (min (H0 * H2) (H1 * H2)) : ℕ) : ℝ) *
      (((v0 * v1 * v2 : ℕ) : ℝ) ^ tau)) :
    HasTauValueAtLeast (threeStarCyclicProduct X Y Z) tau V := by sorry
