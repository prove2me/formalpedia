-- Prove2me | Theorems.Thm_mme_CW_q6_fixed_z_difference_code_injective
-- name    : mme_CW_q6_fixed_z_difference_code_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:14:39.577585+00:00
-- url     : https://prove2.me/theorems/9de0024a-7586-4578-ab97-f8ce8dfd00c7
-- title:
--   The q=6 X-minus-Z code is injective on every fixed-Z fiber
-- statement:
--   Let $M>2$ and assume $2$ is invertible modulo $M$. For an exact coupled q=6 address $e$, form the coefficient word
--
--   $$
--   c_e(j)=2x_e(j)-\operatorname{code}(z_e(j))\pmod M.
--   $$
--
--   Within any fixed Z-word fiber, the map $e\mapsto c_e$ is injective. Indeed, equality of the coefficient words cancels the common Z part and the unit $2$, giving equality of the X-words. The four q=6 supported coordinate types then make the Y-word uniquely determined by X and Z. This controls the size of both equal-code and opposite-code dependency classes in the fixed-Z second moment.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), q=6 first-hash address structure on journal pp. 270--271

import Mathlib
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

open MME

set_option autoImplicit false

theorem mme_CW_q6_fixed_z_difference_code_injective
    {M N L G : ℕ} [NeZero M]
    (hM : 2 < M)
    (h2 : IsUnit (2 : ZMod M))
    (e f : CWQ6ExactCoupledAddress N L G)
    (hz : e.1 2 = f.1 2)
    (hcode :
      (fun j =>
        (2 * ((e.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) =
      (fun j =>
        (2 * ((f.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (f.1 2 j) : ZMod M))) :
    e = f := by
  sorry
