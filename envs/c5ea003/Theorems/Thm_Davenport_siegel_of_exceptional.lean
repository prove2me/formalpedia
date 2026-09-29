-- Prove2me | Theorems.Thm_Davenport_siegel_of_exceptional
-- name    : Davenport.siegel_of_exceptional
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-09-03T22:33:24.216456+00:00
-- url     : https://prove2.me/theorems/abd68937-3a2c-4c76-a736-b2e2d9b7c599
-- title:
--   Siegel's bound from an exceptional real zero
-- statement:
--   **Siegel's bound in the presence of an exceptional real zero** (Davenport §21, first case).
--
--   Suppose some real primitive non-principal character $\chi_1$ modulo $q_1$ has a real zero $\beta$ with $\tfrac{19}{20}\le\beta<1$ lying very close to $1$, namely $1-\beta\le\delta/12$. Then there is a constant $C>0$ such that
--   $$L(1,\chi) \;>\; C\,q^{-\delta}$$
--   for **every** real primitive non-principal character $\chi$ modulo $q$.
--
--   This is the half of Siegel's argument that exploits a hypothetical Siegel zero. One forms the auxiliary product $F(s)=\zeta(s)L(s,\chi_1)L(s,\chi)L(s,\chi_1\chi)$, whose Dirichlet coefficients are nonnegative with constant term $1$, and writes $F=\zeta\cdot f$ with $f=L(\cdot,\chi_1)L(\cdot,\chi)L(\cdot,\chi_1\chi)$. Because $L(\beta,\chi_1)=0$ we have $f(\beta)=0$, so Estermann's lemma applies at $\sigma=\beta$ and yields $f(1)\ge\tfrac14(1-\beta)M^{-3(1-\beta)}$, where $M$ bounds $|f|$ on the disc $|s-2|\le\tfrac32$ and is polynomial in $q_1q$. Dividing by the factors $L(1,\chi_1)$ and $L(1,\chi_1\chi)$, which are bounded above by $6\log(q_1q)$, and using $1-\beta\le\delta/12$ to control the exponent, gives the stated bound.
--
--   *Note.* The constant $C$ depends on the fixed character $\chi_1$ and hence, through $\delta$, is not effectively computable — this is the origin of the celebrated ineffectivity of Siegel's theorem.
-- source:
--   H. Davenport, Multiplicative Number Theory, 3rd ed., Springer GTM 74, §21 (pp. 126-128), Siegel's theorem

import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Davenport

theorem siegel_of_exceptional (δ : ℝ) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 20)
    (q₁ : ℕ) [NeZero q₁] (χ₁ : DirichletCharacter ℂ q₁)
    (hq₁ : χ₁.IsQuadratic) (hn₁ : χ₁ ≠ 1) (hp₁ : χ₁.IsPrimitive)
    (β : ℝ) (hβ : 19 / 20 ≤ β) (hβ₁ : β < 1) (hzero : DirichletCharacter.LFunction χ₁ β = 0)
    (hclose : 1 - β ≤ δ / 12) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsQuadratic → χ ≠ 1 → χ.IsPrimitive →
          C * (q : ℝ) ^ (-δ) < (DirichletCharacter.LFunction χ 1).re := by
  sorry

end Davenport
