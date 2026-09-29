-- Prove2me | Theorems.Thm_mme_ZMod_two_linear_hash_finset_fiber_card_le
-- name    : mme_ZMod_two_linear_hash_finset_fiber_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T04:23:31.222699+00:00
-- url     : https://prove2.me/theorems/cec3b35d-4988-48fe-8364-710ab660232b
-- title:
--   Finite-label fibers of two independent linear hashes
-- statement:
--   Let two linear forms on $(\mathbb Z/p\mathbb Z)^{n+2}$ have a unit $2\times2$ coefficient minor. If the first form is restricted to a finite label set $S$ and the second is fixed at one value $t$, then at most
--
--   $$|S|p^n$$
--
--   parameter vectors satisfy both conditions. This is the finite-label version of exact two-linear-form fiber counting used for the DWZ per-collision bound.
-- source:
--   Elementary finite-field incidence counting, applied to Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Section 3.10, Lemma 3.11 and the per-pair collision estimate on printed pp. 26–27.

import Mathlib
import Theorems.Thm_mme_ZMod_two_linear_hash_fiber_card

open BigOperators
set_option autoImplicit false

theorem mme_ZMod_two_linear_hash_finset_fiber_card_le
    {p n : ℕ} [NeZero p]
    (c d : Fin (n + 2) → ZMod p)
    (j k : Fin (n + 2))
    (hdet : IsUnit (c j * d k - c k * d j))
    (S : Finset (ZMod p)) (t : ZMod p) :
    ((Finset.univ.filter (fun w : Fin (n + 2) → ZMod p ↦
      (∑ i, c i * w i) ∈ S ∧ (∑ i, d i * w i) = t)).card) ≤
        S.card * p ^ n := by
  sorry
