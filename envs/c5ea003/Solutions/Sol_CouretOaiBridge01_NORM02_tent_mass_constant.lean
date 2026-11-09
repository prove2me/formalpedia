-- Prove2me | solution 1 for CouretOaiBridge01.NORM02.tent_mass_constant
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:00:40.076839+00:00
-- url     : https://prove2.me/submissions/3ff69086-5b89-4015-9a71-0e80727a4787

import Mathlib
import Mathlib

/-!
# NORM-02 — finite arithmetic certification layer

This file formalizes elementary, reusable sublemmas of NORM-01:
* exact coverage of the middle tent window by fixed anchor indices;
* primality and coprimality of those anchor indices;
* unique prime label for small-index centers;
* finite bad-square counting budget;
* the rational constant 3/50 in the mass lower bound.

Not formalized here: the 2026 Matomäki–Radziwill–Shao–Tao–Teräväinen
short-interval theorem, the asymptotic exceptional-set estimate, the full
squarefree sieve or the normalized Möbius correlation asymptotics.

RESEARCH ONLY. No sorry, no axioms added, no RH claim, no novelty claim.
-/

namespace CouretOaiBridge01
namespace NORM02













/-- Multiplying the two tent-weight lower bounds and the good-shift
count gives the precise rational factor 3/50. -/
theorem p2m_local_tent_mass_constant
    (H V : ℚ)
    (hV : (2 / 5 : ℚ) * (3 / 10) * (H / 2) ≤ V) :
    (3 / 50 : ℚ) * H ≤ V := by
  linarith

end NORM02
end CouretOaiBridge01

theorem solution : ∀ (H V : Rat),
  @LE.le.{0} Rat Rat.instLE
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))
            (@OfNat.ofNat.{0} Rat (nat_lit 5) (@Rat.instOfNat (nat_lit 5))))
          (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
            (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3)))
            (@OfNat.ofNat.{0} Rat (nat_lit 10) (@Rat.instOfNat (nat_lit 10)))))
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv) H
          (@OfNat.ofNat.{0} Rat (nat_lit 2) (@Rat.instOfNat (nat_lit 2)))))
      V →
    @LE.le.{0} Rat Rat.instLE
      (@HMul.hMul.{0, 0, 0} Rat Rat Rat (@instHMul.{0} Rat Rat.instMul)
        (@HDiv.hDiv.{0, 0, 0} Rat Rat Rat (@instHDiv.{0} Rat Rat.instDiv)
          (@OfNat.ofNat.{0} Rat (nat_lit 3) (@Rat.instOfNat (nat_lit 3)))
          (@OfNat.ofNat.{0} Rat (nat_lit 50) (@Rat.instOfNat (nat_lit 50))))
        H)
      V := @_root_.CouretOaiBridge01.NORM02.p2m_local_tent_mass_constant

