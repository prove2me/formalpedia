-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_kron_of_each_strict_below_product
-- name    : mme_HasTauValueAtLeast_kron_of_each_strict_below_product
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-09T04:20:46.562751+00:00
-- url     : https://prove2.me/theorems/76f3744f-51d4-4483-b327-135303c3dd74
-- title:
--   Binary Kronecker multiplicativity of the tau-value
-- statement:
--   **Multiplicativity of the asymptotic tau-value under a two-factor Kronecker product.**
--
--   Let $X$ and $Y$ be order-three tensors over a field $K$, let $\tau$ be a real exponent, and let
--   $e_X, e_Y > 0$ be strict value endpoints, meaning that $X$ has tau-value at least $V$ for every
--   $0 \le V < e_X$ and $Y$ has tau-value at least $V$ for every $0 \le V < e_Y$.
--
--   Then the Kronecker product $X \otimes Y$ has tau-value at least $W$ for every
--   $0 \le W < e_X e_Y$.
--
--   This is the two-factor case of the standard fact that Coppersmith--Winograd values multiply under
--   tensor products, in the strict-endpoint form the extraction arguments actually consume: one never
--   has a value *at* the endpoint, only below it, and the conclusion is again an endpoint statement so
--   the lemma composes with itself.
--
--   The platform already has the $n$-factor version phrased through `TensorObj.kronFin` and a vector of
--   multiplicities (`mme_HasTauValueAtLeast_kronFin_multiplicities_of_each_strict_below_product`), but
--   the tensors that arise from the fine-to-coarse constituent restrictions of the fourth-power laser
--   method are literal binary products `TensorObj.kron X Y`, not `kronFin` expressions.  The two differ
--   by trailing unit factors: `kronFin 2 (fun i => (![X,Y] i).kronPow 1)` unfolds to
--   `kron (kron X 1) (kron (kron Y 1) 1)`.  They are isomorphic, hence equal in the isomorphism
--   quotient `TensorQ`, so the value transports along `mme_HasTauValueAtLeast_mono_restrict`.
--
--   Together with `mme_dwz_fourth_pair_factor_restrictions_to_coarse`, which turns a pair of square
--   constituent restrictions into one fourth-power coarse-block restriction, this lemma is exactly the
--   step that converts a pair of square component values into a fourth-power block value.
-- source:
--   R. Duan, H. Wu and R. Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, Section 2.4 (values are multiplicative under tensor product); arXiv:2210.10173. See also D. Coppersmith and S. Winograd, Matrix multiplication via arithmetic progressions, J. Symbolic Computation 9 (1990), Section 6.

import Definitions.Def_mme_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_HasTauValueAtLeast_kron_of_each_strict_below_product
    {K : Type u} [Field K]
    (X Y : TensorObj K 3) (tau eX eY : ℝ)
    (heX : 0 < eX) (heY : 0 < eY)
    (hX : ∀ V : ℝ, 0 ≤ V → V < eX → HasTauValueAtLeast X tau V)
    (hY : ∀ V : ℝ, 0 ≤ V → V < eY → HasTauValueAtLeast Y tau V) :
    ∀ W : ℝ, 0 ≤ W → W < eX * eY →
      HasTauValueAtLeast (TensorObj.kron X Y) tau W := by
  sorry
