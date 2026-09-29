-- Prove2me | Theorems.Thm_WittVector_exists_valuationSubring_residueField_equiv_of_isAlgebraic
-- name    : WittVector.exists_valuationSubring_residueField_equiv_of_isAlgebraic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/4c13503c-b432-57f9-8fd7-e8fee8654774
-- title:
--   Valuation subring of an algebraic extension of W(k) dominating W(k)
-- statement:
--   Let $p$ be a prime and let $k$ be an algebraically closed field of characteristic $p$, so that the Witt vector ring $W(k) =$ `WittVector p k` is a local ring. Let $\Omega$ be a field equipped with a $W(k)$-algebra structure whose structure map is injective (the faithfulness of the scalar action) and such that $\Omega$ is algebraic over $W(k)$. The assertion is that there exist a valuation subring $V \subseteq \Omega$, a proof $hV$ that $V$ contains the image of every $a \in W(k)$ under the structure map, and a ring isomorphism $\varphi$ from $k$ onto the residue field of the local ring $V$, such that: (i) $V$ dominates $W(k)$, in the sense that for every $a$ in the maximal ideal of $W(k)$ the image of $a$ in $\Omega$ is a non-unit of $V$; and (ii) $\varphi$ matches the two reduction maps, namely $\varphi(a_0)$ equals the residue class in the residue field of $V$ of the element of $V$ given by the image of $a$, for every $a \in W(k)$, where $a_0 =$ `a.coeff 0` is the zeroth Witt coordinate of $a$.
--
--   This is Chevalley's valuation extension theorem specialised to the complete discrete valuation ring $W(k)$ and an algebraic extension field of it, together with the resulting identification of the residue field of the extended valuation with $k$. It fixes the characteristic-zero base for the local part of Deuring's lifting theorem, and is used in the construction of good constant reductions of algebraic curves and in lifting Vélu quotients together with their two- and three-torsion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_WittVector_exists_valuationSubring_residueField_equiv_of_isAlgebraic.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem WittVector.exists_valuationSubring_residueField_equiv_of_isAlgebraic (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [IsAlgClosed k] [CharP k p] (Ω : Type*) [Field Ω] [Algebra (WittVector p k) Ω] [FaithfulSMul (WittVector p k) Ω] [Algebra.IsAlgebraic (WittVector p k) Ω] : ∃ (V : ValuationSubring Ω) (hV : ∀ a : WittVector p k, algebraMap (WittVector p k) Ω a ∈ V) (φ : k ≃+* IsLocalRing.ResidueField V), (∀ a ∈ IsLocalRing.maximalIdeal (WittVector p k), algebraMap (WittVector p k) Ω a ∈ V.nonunits) ∧ ∀ a : WittVector p k, φ (a.coeff 0) = IsLocalRing.residue V ⟨algebraMap (WittVector p k) Ω a, hV a⟩ := by sorry
