-- Prove2me | solution 1 for mme_sixSymmetrization_uniform_bigAdd_isomorphic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T16:57:52.123975+00:00
-- url     : https://prove2.me/submissions/a27a976b-c922-4466-ac17-1abbdb44238d

import Definitions.Def_mme_six_symmetrized_tau_value
import Definitions.Def_mme_rank_bridge
import Definitions.Def_mme_cyclicSymmetrization_public_perm
import Mathlib.Tactic

open MME MME.TensorObj

universe u

set_option autoImplicit false

/-!
# Six-symmetrizing a uniform direct sum multiplies the copies by six powers

`sixSymmetrization` is a Kronecker product of six permuted copies of its argument, so applying it
to a direct sum of `k` identical summands distributes into `k ^ 6` copies of the six-symmetrization
of one summand. The identity is exact, not merely a restriction in one direction.
-/

theorem solution {K : Type u} [Field K] (T : TensorObj K 3) (k : ℕ) :
    Isomorphic (sixSymmetrization (bigAdd (fun _ : Fin k ↦ T)))
      (bigAdd (fun _ : Fin (k ^ 6) ↦ sixSymmetrization T)) := by
  apply TensorQ.toQ_eq_iff.mp
  simp only [sixSymmetrization, cyclicSymmetrization_eq_public_perm, TensorQ.toQ_bigAdd,
    TensorQ.toQ_kron, ← TensorQ.permAut_toQ,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, map_mul, map_natCast]
  ring
