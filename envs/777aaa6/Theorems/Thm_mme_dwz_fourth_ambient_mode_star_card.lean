-- Prove2me | Theorems.Thm_mme_dwz_fourth_ambient_mode_star_card
-- name    : mme_dwz_fourth_ambient_mode_star_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-17T20:35:51.850607+00:00
-- url     : https://prove2.me/theorems/3960a3ed-ff1d-43df-a7b7-388448f70f0a
-- title:
--   Exact full ambient mode-star cardinality for the fourth-level CW support
-- statement:
--   Let $N\geq0$ and let $M_i(g)$ be arbitrary nonnegative integer marginal counts, for $i\in\{X,Y,Z\}$ and $g\in\{0,\ldots,8\}$. Define the fourth-level support
--   $$
--   \mathcal C=\{(i,j,k)\in\{0,\ldots,8\}^3:i+j+k=8\}.
--   $$
--   Choose a mode $s$ and a word $x:[N]\to\{0,\ldots,8\}$ whose histogram is $M_s$. Let $\mathcal H(M)$ contain all bounded integer tables $h:\mathcal C\to\{0,\ldots,N\}$ satisfying all three marginal conditions:
--   $$
--   \sum_{\sigma:\sigma_i=g}h_\sigma=M_i(g)
--   \quad\text{for every }i\in\{X,Y,Z\},\ g\in\{0,\ldots,8\}.
--   $$
--   The full ambient $s$-star consists of every triple of words $(a_X,a_Y,a_Z)$ with coordinatewise sum $8$, marginal histograms $M_X,M_Y,M_Z$, and $a_s=x$. Its exact cardinality is
--   $$
--   \left|\left\{a:\ a_X(t)+a_Y(t)+a_Z(t)=8,\
--   \operatorname{hist}(a_i)=M_i,\ a_s=x\right\}\right|
--   =
--   \sum_{h\in\mathcal H(M)}
--   \prod_{g=0}^{8}
--   \frac{M_s(g)!}{\prod_{\sigma:\sigma_s=g}h_\sigma!}.
--   $$
--   Each quotient is natural-number division and is an exact integer multinomial on admissible tables. The sum runs over all compatible joint tables, not just a distinguished target table. The three marginals may differ, zero rows and $N=0$ are included, and incompatible marginal data give zero on both sides. No separate total-mass hypothesis is required beyond the prescribed histogram of $x$. This is an exact finite counting result; it does not assume or establish an entropy optimization or a hash-degree estimate for an arbitrarily indexed ambient family.
-- source:
--   Derived exact finite ambient-star count from Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 3.7 (types and multinomial counts), Section 3.10 (partition into joint distributions and Lemma 3.12), and Section 6.2 (ambient hash-isolation competitors). https://arxiv.org/html/2210.10173v5 . The proof specializes the proved constrained prescribed-fiber counting theorem to the fourth-level support and sums actual histogram fibers; no symmetry of the three marginals is assumed.

import Theorems.Thm_mme_fintype_constrained_prescribed_fiber_function_card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Logic.Equiv.Basic


open BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_dwz_fourth_ambient_mode_star_card (N : ℕ) (M : Fin 3 → Fin 9 → ℕ)
    (mode : Fin 3) (x : Fin N → Fin 9)
    (hx : ∀ g, Fintype.card {t : Fin N // x t = g} = M mode g) :
    let Cell := {sigma : Fin 3 → Fin 9 // (∑ i, (sigma i).val) = 8}
    let admissible : Finset (Cell → Fin (N + 1)) := Finset.univ.filter (fun h ↦
      ∀ i : Fin 3, ∀ g : Fin 9,
        (∑ sigma : {sigma : Cell // sigma.val i = g}, (h sigma.val).val) = M i g)
    Nat.card {a : Fin 3 → Fin N → Fin 9 //
      (∀ t, (∑ i, (a i t).val) = 8) ∧
      (∀ i g, Fintype.card {t : Fin N // a i t = g} = M i g) ∧ a mode = x} =
      ∑ h ∈ admissible, ∏ g : Fin 9,
        (M mode g).factorial /
          ∏ sigma : {sigma : Cell // sigma.val mode = g},
            ((h sigma.val).val).factorial := by sorry
