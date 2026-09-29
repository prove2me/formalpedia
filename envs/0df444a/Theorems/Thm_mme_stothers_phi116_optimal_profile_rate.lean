-- Prove2me | Theorems.Thm_mme_stothers_phi116_optimal_profile_rate
-- name    : mme_stothers_phi116_optimal_profile_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T08:19:56.092997+00:00
-- url     : https://prove2.me/theorems/6b2ee772-9b6f-416b-86e1-7575fc71d6dc
-- title:
--   Davie--Stothers $\phi_{116}$: exact legal profile attaining $4(E^2+2L)$
-- statement:
--   Let $E,L>0$. Define the recursive type frequency
--
--   $$
--   a=\frac{2L}{2L+E^2}.
--   $$
--
--   Then $0<a<1$, and the two-type asymptotic profile rate satisfies the exact identity
--
--   $$
--   4\left(\frac{2L}{a}\right)^a\left(\frac{E^2}{1-a}\right)^{1-a}=4(E^2+2L).
--   $$
--
--   In the fourth-power Coppersmith--Winograd analysis, $E=(2q)^\rho$ is the rectangular constituent contribution and $L=4q^\rho(q^\rho+2)$ is the cubed cyclic value of $\phi_{112}$. Consequently, this theorem supplies exactly the optimized constituent value $V_{116}(\rho)^3\ge 4(E^2+2L)$ used in Davie--Stothers Lemma 5.1(i). The strict interval conclusion ensures that the frequency is admissible for the finite type extraction.
-- source:
--   A. M. Davie and A. J. Stothers, Improved bound for complexity of matrix multiplication, Proc. Royal Soc. Edinburgh A 143 (2013), printed p. 364, Lemma 5.1(i) and the optimization by Lemma 3.4; https://www.maths.ed.ac.uk/~sandy/a11164.pdf . See also A. J. Stothers, On the Complexity of Matrix Multiplication, PhD thesis (2010), Chapter 4.3, Lemma 21, printed pp. 81--83, for the detailed count resolving the journal display's missing factor two; https://era.ed.ac.uk/bitstream/handle/1842/4734/Stothers2010.pdf

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

theorem mme_stothers_phi116_optimal_profile_rate
    (E L : ℝ) (hE : 0 < E) (hL : 0 < L) :
    let a := (2 * L) / (2 * L + E ^ (2 : ℕ))
    0 < a ∧ a < 1 ∧
      4 *
          (((2 * L) / a) ^ a *
            ((E ^ (2 : ℕ)) / (1 - a)) ^ (1 - a)) =
        4 * (E ^ (2 : ℕ) + 2 * L) := by sorry
