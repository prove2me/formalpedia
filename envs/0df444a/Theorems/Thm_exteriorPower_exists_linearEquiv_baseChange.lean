-- Prove2me | Theorems.Thm_exteriorPower_exists_linearEquiv_baseChange
-- name    : exteriorPower.exists_linearEquiv_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/cb437c70-675e-53fc-9440-d80a25bf3dc8
-- title:
--   Exterior powers commute with base change
-- statement:
--   Let $R$ be a commutative ring, $A$ a commutative $R$-algebra, $M$ an $R$-module (an additive commutative group with an $R$-module structure) and $n$ a natural number. The assertion is that there exists an isomorphism of $A$-modules
--   $$e : A \otimes_R \textstyle\bigwedge_R^n M \;\xrightarrow{\sim}\; \textstyle\bigwedge_A^n (A \otimes_R M),$$
--   where the source carries its $A$-module structure coming from the left tensor factor and the target is the $n$-th exterior power over $A$ of the base change $A \otimes_R M$, such that for every $a \in A$ and every family $m : \mathrm{Fin}\, n \to M$ one has
--   $$e\bigl(a \otimes (m_1 \wedge \cdots \wedge m_n)\bigr) = a \cdot \bigl((1 \otimes m_1) \wedge \cdots \wedge (1 \otimes m_n)\bigr),$$
--   the wedge products being the values of Mathlib's canonical alternating maps `exteriorPower.ιMulti R n` and `exteriorPower.ιMulti A n` on the indicated families. No finiteness, freeness or flatness hypothesis is imposed on $M$, and none on $A$ beyond being a commutative $R$-algebra. Note that the statement is purely existential: it provides an equivalence with the displayed behaviour on pure tensors of pure wedges, without naming a particular map and without asserting uniqueness (which would follow, as such elements generate the source).
--
--   This is the standard compatibility of exterior powers with extension of scalars. It is used to transfer exterior powers along localisation maps, and is cited here by [`IsLocalizedModule.of_forall_apply_iotaMulti_eq`](thm.html#IsLocalizedModule.of_forall_apply_iotaMulti_eq), which recognises a module equipped with a map behaving like wedge products of localised elements as a localisation of an exterior power.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exteriorPower_exists_linearEquiv_baseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct

theorem exteriorPower.exists_linearEquiv_baseChange
    (R : Type*) [CommRing R] (A : Type*) [CommRing A] [Algebra R A]
    (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    ∃ e : A ⊗[R] (⋀[R]^n M) ≃ₗ[A] ⋀[A]^n (A ⊗[R] M),
      ∀ (a : A) (m : Fin n → M),
        e (a ⊗ₜ exteriorPower.ιMulti R n m) =
          a • exteriorPower.ιMulti A n (fun i => (1 : A) ⊗ₜ[R] m i) := by sorry
