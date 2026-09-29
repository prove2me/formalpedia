-- Prove2me | Theorems.Thm_cyclotomicCharacter_algebraicClosure_rat_surjective
-- name    : cyclotomicCharacter_algebraicClosure_rat_surjective
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:23:47.845422+00:00
-- url     : https://prove2.me/theorems/6a3e3302-509f-4b2a-994d-53b076b34188
-- title:
--   The $p$-adic cyclotomic character of $\mathbb Q$ is surjective
-- statement:
--   Let $p$ be a prime, $\overline{\mathbb Q}$ an algebraic closure of $\mathbb Q$ and $G_{\mathbb Q}=\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$. The $p$-adic cyclotomic character
--   $$\chi_p : G_{\mathbb Q}\longrightarrow \mathbb Z_p^\times,\qquad \sigma(\zeta)=\zeta^{\chi_p(\sigma)}\ \text{ for all } \zeta\in\mu_{p^\infty}(\overline{\mathbb Q}),$$
--   is surjective.
--
--   Equivalently, $\mathrm{Gal}(\mathbb Q(\mu_{p^\infty})/\mathbb Q)\cong\mathbb Z_p^\times$; at each finite level this is the classical isomorphism $\mathrm{Gal}(\mathbb Q(\zeta_{p^n})/\mathbb Q)\cong(\mathbb Z/p^n\mathbb Z)^\times$, i.e. the irreducibility of the cyclotomic polynomials over $\mathbb Q$. The surjectivity of $\chi_p$ is the basic input for constructing abelian pro-$p$ extensions of $\mathbb Q$ such as the cyclotomic $\mathbb Z_p$-extension.
--
--   **Formalization Note** $\chi_p$ is Mathlib's `cyclotomicCharacter`, composed with the action of $G_{\mathbb Q}$ on $\overline{\mathbb Q}$ by ring automorphisms.
-- source:
--   L. C. Washington, Introduction to Cyclotomic Fields, 2nd ed., GTM 83, Theorem 2.5 (Gal(Q(ζ_n)/Q) ≅ (Z/nZ)^×) and §13.1 (Gal(Q(μ_{p^∞})/Q) ≅ Z_p^×).

import Mathlib.NumberTheory.Cyclotomic.CyclotomicCharacter
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

theorem cyclotomicCharacter_algebraicClosure_rat_surjective (p : ℕ) [Fact p.Prime] :
    Function.Surjective ((cyclotomicCharacter (AlgebraicClosure ℚ) p).comp
      (MulSemiringAction.toRingAut Gal(AlgebraicClosure ℚ/ℚ) (AlgebraicClosure ℚ))) := by sorry
