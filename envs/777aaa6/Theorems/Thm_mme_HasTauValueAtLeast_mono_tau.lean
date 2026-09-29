-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_mono_tau
-- name    : mme_HasTauValueAtLeast_mono_tau
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T08:52:17.557006+00:00
-- url     : https://prove2.me/theorems/66c72199-bdeb-43d6-a945-7aa88480eca6
-- title:
--   Tau-value witnesses are monotone in every positive exponent parameter
-- statement:
--   Let $T$ be an order-three tensor over a field and let $0<\tau\le\tau'$. If $T$ has tau-value at least $V$ at parameter $\tau$, then it has tau-value at least $V$ at parameter $\tau'$.
--
--   The proof reuses every finite direct-sum extraction. A matrix-product summand of positive volume has an integer volume at least one, so its real power is nondecreasing in the exponent. A zero-volume summand has weight zero at both positive parameters. The positivity hypothesis is necessary for the witness-level definition: at parameter zero, a zero-volume summand would instead have weight $0^0=1$.
-- source:
--   The monotonicity of the tensor tau-value in its exponent parameter, implicit in A. Schönhage, Partial and Total Matrix Multiplication, SIAM J. Comput. 10(3), 1981, and in D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, J. Symbolic Computation 9, 1990, journal p. 264.

import Definitions.Def_mme_tau_value

open MME BigOperators Filter

universe u

theorem mme_HasTauValueAtLeast_mono_tau
    {K : Type u} [Field K] {T : TensorObj K 3} {tau tau' V : ℝ}
    (htau : 0 < tau) (htau' : tau ≤ tau')
    (hV : HasTauValueAtLeast T tau V) :
    HasTauValueAtLeast T tau' V := by sorry
