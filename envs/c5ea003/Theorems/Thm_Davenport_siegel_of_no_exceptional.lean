-- Prove2me | Theorems.Thm_Davenport_siegel_of_no_exceptional
-- name    : Davenport.siegel_of_no_exceptional
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-09-03T22:33:23.72382+00:00
-- url     : https://prove2.me/theorems/6ffd846d-e7f8-4840-b219-0b6e509699d2
-- title:
--   Siegel's bound in the absence of an exceptional real zero
-- statement:
--   **Siegel's bound when no exceptional real zero exists** (Davenport §21, second case).
--
--   Assume that no real primitive non-principal character has a real zero in the interval $[1-\delta/12,\,1)$. Then there is a constant $C>0$ with
--   $$L(1,\chi)\;>\;C\,q^{-\delta}$$
--   for every real primitive non-principal character $\chi$ modulo $q$.
--
--   Here the auxiliary product $F(s)=\zeta(s)L(s,\chi_1)L(s,\chi)L(s,\chi_1\chi)$ is formed with a *fixed* auxiliary character $\chi_1$, and Estermann's lemma is applied at the point $\sigma=1-\delta/12$ itself. The hypothesis guarantees that none of the three $L$-factors vanishes on $[\sigma,1]$; since each is positive at $s=1$ and continuous, each is positive at $\sigma$, so $f(\sigma)>0$ and the lemma applies. The resulting lower bound $f(1)\ge\tfrac14(1-\sigma)M^{-3(1-\sigma)}$ again gives the claim after dividing out the bounded factors.
--
--   Together with the companion statement `Davenport.siegel_of_exceptional`, which handles the opposite case, this yields Siegel's theorem: one splits on whether an exceptional zero exists, and the two cases are exhaustive.
-- source:
--   H. Davenport, Multiplicative Number Theory, 3rd ed., Springer GTM 74, §21 (pp. 126-128), Siegel's theorem

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Davenport

theorem siegel_of_no_exceptional (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 20)
    (hno : ∀ (q₁ : ℕ) [NeZero q₁] (χ₁ : DirichletCharacter ℂ q₁),
      χ₁.IsQuadratic → χ₁ ≠ 1 → χ₁.IsPrimitive →
        ∀ β : ℝ, 1 - δ / 12 ≤ β → β < 1 → DirichletCharacter.LFunction χ₁ β ≠ 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsQuadratic → χ ≠ 1 → χ.IsPrimitive →
          C * (q : ℝ) ^ (-δ) < (DirichletCharacter.LFunction χ 1).re := by
  sorry

end Davenport
