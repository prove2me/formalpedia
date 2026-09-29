-- Prove2me | Theorems.Thm_WittVector_exists_valuationSubring_lift_with_transcendental
-- name    : WittVector.exists_valuationSubring_lift_with_transcendental
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/62aa2a43-b423-54fe-8d4a-ecb609ffa335
-- title:
--   Witt lift into a valuation ring with a transcendental element
-- statement:
--   Let $p$ be a prime and let $K$ be a field of characteristic $p$ in universe $u$ whose Frobenius is bijective (`PerfectRing K p`). The assertion is the existence of the following data: a type $L$ in the same universe $u$, carrying a field structure, algebraically closed and of characteristic zero; a valuation subring $A$ of $L$; a ring homomorphism $\varphi \colon W(K) \to L$ from the ring of $p$-typical Witt vectors of $K$, together with a proof that $\varphi(x) \in A$ for every $x$; and a ring homomorphism $\iota \colon K \to \kappa_A$ into the residue field of the local ring $A$, such that two conditions hold. First, for every $a \in K$ the element $\varphi([a]) \in A$, where $[\,\cdot\,]$ is the Teichmüller map `WittVector.teichmuller p`, has residue class $\iota(a)$ in $\kappa_A$. Second, there is an element $t$ of $L$ lying in $A$ whose image in $A$ belongs to the maximal ideal of $A$, and which is transcendental over $\varphi(W(K))$ in the following precise sense: for every nonzero polynomial $P \in W(K)[X]$, the value $\mathrm{eval}_2(\varphi, t)(P)$, that is $\sum_i \varphi(c_i) t^i$ for $P = \sum_i c_i X^i$, is nonzero. (Injectivity of $\varphi$ and of $\iota$, and $t \neq 0$, are consequences but are not part of the statement.)
--
--   This is a mixed-characteristic lifting device: it produces a characteristic-zero algebraically closed field with a valuation subring receiving $W(K)$, compatibly with the Teichmüller section over an embedding of $K$ into the residue field, together with a free parameter $t$ in the maximal ideal transcendental over the image of $W(K)$. It is used to lift objects over $K$ (for instance Weierstrass equations) to $A$ without changing their reduction while allowing a deformation by $t$; in this development it is cited in the analysis of fibre polynomials of modular polynomial data, in [`ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental`](thm.html#ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_fullKernelQuotient_j_of_transcendental) and [`ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j`](thm.html#ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_exists_valuationSubring_lift_with_transcendental.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem WittVector.exists_valuationSubring_lift_with_transcendental
    (p : ℕ) [Fact p.Prime] (K : Type u) [Field K] [CharP K p] [PerfectRing K p] :
    ∃ (L : Type u) (_ : Field L) (_ : IsAlgClosed L) (_ : CharZero L)
      (A : ValuationSubring L) (φ : WittVector p K →+* L) (hφ : ∀ x, φ x ∈ A)
      (ι : K →+* IsLocalRing.ResidueField A),
      (∀ a : K, IsLocalRing.residue A ⟨φ (WittVector.teichmuller p a), hφ _⟩ = ι a) ∧
      ∃ (t : L) (ht : t ∈ A), (⟨t, ht⟩ : A) ∈ IsLocalRing.maximalIdeal A ∧
        ∀ P : Polynomial (WittVector p K), P ≠ 0 → P.eval₂ φ t ≠ 0 := by sorry
