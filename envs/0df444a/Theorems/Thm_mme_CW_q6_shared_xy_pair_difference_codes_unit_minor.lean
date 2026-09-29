-- Prove2me | Theorems.Thm_mme_CW_q6_shared_xy_pair_difference_codes_unit_minor
-- name    : mme_CW_q6_shared_xy_pair_difference_codes_unit_minor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T23:51:04.712978+00:00
-- url     : https://prove2.me/theorems/2769c3b5-1d1d-4e75-9955-ba4edf7515ca
-- title:
--   A distinct q=6 pair sharing X or Y has independent difference-hash codes
-- statement:
--   For an exact coupled q=6 address e, let c_e be its X-minus-Z difference-hash coefficient word over Z/MZ. If two distinct exact addresses e and f share either their complete X-word or their complete Y-word, then two coordinates j,k give a unit determinant: $$c_e(j)c_f(k)-c_e(k)c_f(j)\in(\mathbb Z/M\mathbb Z)^\times.$$ Consequently the two difference-hash equations are jointly uniform. The result uses the exact common Z-grade-2 multiplicity 2G and is the finite linear-algebra kernel for counting X/Y collision parameters; it makes no pruning or tensor-realization claim.
-- source:
--   CW90 q=6 affine-hash collision independence for distinct addresses sharing an X- or Y-word

import Mathlib
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_shared_xy_pair_difference_codes_unit_minor
    {M N L G : ℕ} [NeZero M]
    (e f : CWQ6ExactCoupledAddress N L G)
    (hne : e ≠ f)
    (hshare : e.1 0 = f.1 0 ∨ e.1 1 = f.1 1) :
    ∃ j k : Fin (2 * N), IsUnit (
      ((2 * ((e.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) *
        ((2 * ((f.1 0 k).val : ZMod M)) -
          (cwQ6CoupledZHashCode (f.1 2 k) : ZMod M)) -
      ((2 * ((e.1 0 k).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1 2 k) : ZMod M)) *
        ((2 * ((f.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (f.1 2 j) : ZMod M))) := by
  sorry
