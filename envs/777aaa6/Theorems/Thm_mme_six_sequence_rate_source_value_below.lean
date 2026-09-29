-- Prove2me | Theorems.Thm_mme_six_sequence_rate_source_value_below
-- name    : mme_six_sequence_rate_source_value_below
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T11:28:00.810566+00:00
-- url     : https://prove2.me/theorems/6274d658-a8c9-46da-bc98-35285c3a4345
-- title:
--   Sequence rates below a fixed tensor source
-- statement:
--   Let $T$ be a tensor over a field $K$, and let $A_m$ be tensors with integer lengths $\ell_m$. Suppose $A_m\preceq T^{\otimes\ell_m}$ for every $m$. Assume the sequence has six-symmetrized restriction rate at least $V$: every positive $w<V$ has finite matrix-extraction witnesses of weight at least $w^{6\ell_m}$ at arbitrarily large indices and lengths. Then every $0<v<V$ satisfies
--   $$V^{(6)}_\tau(T)\ge v.$$
--   Here the conclusion uses the existing ordinary six-symmetric tau-value predicate, whose direct value is normalized by $v^6$. This transfers compatible sequence witnesses to a fixed ambient source. It asserts every positive strict lower value, rather than a relative-error witness at the endpoint $V$.
-- source:
--   Derived from the six-sequence witness interface and accepted tensor restriction and power isomorphism theorems.

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_sixSymmetrization_kronPow_isomorphic

open MME MME.DWZRestrictedValue Filter
open scoped BigOperators
universe u
set_option autoImplicit false

theorem mme_six_sequence_rate_source_value_below
    {K : Type u} [Field K] (T : TensorObj K 3)
    (A : ℕ → TensorObj K 3) (length : ℕ → ℕ) (tau V v : ℝ)
    (hrate : HasSixSequenceRate TensorObj.Restrict A length tau V)
    (hsource : ∀ m, TensorObj.Restrict (A m) (T.kronPow (length m)))
    (hv : 0 < v) (hvV : v < V) :
    HasSixSymmetricTauValueAtLeast T tau v := by sorry
