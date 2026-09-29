-- Prove2me | Theorems.Thm_mme_CW_q6_fixed_z_nondependent_pair_unit_minor
-- name    : mme_CW_q6_fixed_z_nondependent_pair_unit_minor
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-24T22:11:45.7082+00:00
-- url     : https://prove2.me/theorems/f9182de0-f811-4ada-970b-0417ecfa2664
-- title:
--   A nondependent fixed-Z q=6 address pair has a unit hash minor
-- statement:
--   Fix two exact coupled q=6 addresses with the same Z-word. For each address form the coefficient word obtained by subtracting the doubled Z-hash coefficients from the doubled X-hash coefficients. Assume the two coefficient words are neither equal nor global negatives, and assume that $2$ is a unit modulo $M$. Then two coordinates $j,k$ give a unit minor
--
--   $$
--   c_e(j)c_f(k)-c_e(k)c_f(j).
--   $$
--
--   Indeed, on every active Z-grade-2 coordinate the coefficient is $+1$ or $-1$. Non-equality supplies an opposite-sign coordinate, while non-oppositeness supplies an equal-sign coordinate, so the minor is a signed unit multiple of $2$. This separates the unique dependent complement class from the jointly uniform pairs in the q=6 fixed-Z second-moment calculation.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), q=6 first-hash collision calculation on journal pp. 270--271; finite sign-vector minor underlying the dependent-pair second moment

import Mathlib
import Definitions.Def_mme_CW_q6_doubled_hash_arithmetic

open BigOperators MME

set_option autoImplicit false

theorem mme_CW_q6_fixed_z_nondependent_pair_unit_minor
    {M N L G : ℕ} [NeZero M]
    (e f : CWQ6ExactCoupledAddress N L G)
    (hz : e.1 2 = f.1 2)
    (hne :
      (fun j =>
        (2 * ((e.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) ≠
      (fun j =>
        (2 * ((f.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (f.1 2 j) : ZMod M)))
    (hnneg :
      (fun j =>
        (2 * ((e.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (e.1 2 j) : ZMod M)) ≠
      (fun j => -(
        (2 * ((f.1 0 j).val : ZMod M)) -
          (cwQ6CoupledZHashCode (f.1 2 j) : ZMod M))))
    (h2 : IsUnit (2 : ZMod M)) :
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
