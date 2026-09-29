-- Prove2me | Theorems.Thm_mme_CW_q6_regular_primary_hash_large_uniform_family
-- name    : mme_CW_q6_regular_primary_hash_large_uniform_family
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T02:55:26.869774+00:00
-- url     : https://prove2.me/theorems/0b684729-420f-4c73-8c42-32794c2a479e
-- title:
--   A large regular q=6 hash bucket yields a uniform induced family
-- statement:
--   For a regular exact q=6 profile, set $X=\binom{n+1}{G}$, $B=\binom{2G}{G}$, $M=4X^2+1$, and let $Z$ be the exact third-mode word family. Let $S\subseteq\{0,\ldots,\lfloor M/2\rfloor-1\}$ be three-term-progression-free. If $G>0$ and $400M\le B$, then there are integers $A,H$ and a genuine uniform induced primary hash family with\n\n$$A\ge\left\lfloor\frac{|S||Z|}{16M}\right\rfloor,\qquad H=\left\lfloor\frac{B}{8M}\right\rfloor.$$\n\nThe family keeps the common third-mode word in each star, so every retained outer fiber has exactly the shared multiplicity $H$ required by the C-tensor construction.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), journal pp. 270–272: q=6 affine hashing, X/Y collision deletion, and uniform common-star truncation; https://doi.org/10.1016/S0747-7171(08)80013-2

import Mathlib
import Theorems.Thm_mme_CW_q6_regular_primary_hash_bucket_large_isolated_many_z_stars
import Theorems.Thm_mme_CW_q6_lower_bounded_isolated_address_set_to_hash_family
import Theorems.Thm_mme_CW_q6_primary_hash_bucket_structure

open BigOperators MME

set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem mme_CW_q6_regular_primary_hash_large_uniform_family
    {n L G : ℕ}
    (hregular : CWQ6ExactAddressRegularity (n + 1) L G)
    (hG : 0 < G)
    (S : Finset ℕ)
    (hSrange : S ⊆ Finset.range
      ((4 * (Nat.choose (n + 1) G) ^ 2 + 1) / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (hlarge :
      400 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1) ≤
        Nat.choose (2 * G) G) :
    ∃ A H : ℕ,
      Nonempty (CWQ6PrimaryHashFamily (n + 1) L G A H) ∧
      (S.card * (cwQ6ExactZWords (n + 1) L G).card) /
            (16 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1)) ≤ A ∧
      H = Nat.choose (2 * G) G /
            (8 * (4 * (Nat.choose (n + 1) G) ^ 2 + 1)) := by
  sorry
