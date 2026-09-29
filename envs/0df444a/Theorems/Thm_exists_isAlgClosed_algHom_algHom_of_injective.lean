-- Prove2me | Theorems.Thm_exists_isAlgClosed_algHom_algHom_of_injective
-- name    : exists_isAlgClosed_algHom_algHom_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/51227177-ff9b-5891-9e51-8cd0b28f2899
-- title:
--   Common algebraically closed D-algebra receiving two field extensions
-- statement:
--   Let $D$ be a commutative ring which is a domain, and let $E_1$ and $E_2$ be fields equipped with $D$-algebra structures whose structure maps $\mathrm{algebraMap}\,D\,E_1$ and $\mathrm{algebraMap}\,D\,E_2$ are injective (hypotheses $h_1$, $h_2$); all three types are taken in the lowest universe. The conclusion asserts the existence of a type $\Omega'$ together with a field structure on it, a proof that $\Omega'$ is algebraically closed, and a $D$-algebra structure on $\Omega'$, such that the type of $D$-algebra homomorphisms $E_1 \to_D \Omega'$ is nonempty and likewise the type of $D$-algebra homomorphisms $E_2 \to_D \Omega'$ is nonempty. Thus both $E_1$ and $E_2$ embed into one algebraically closed field in a way compatible with their $D$-algebra structures; the field structure, the algebraic closedness and the $D$-algebra structure on $\Omega'$ are all part of the existential data, and the two homomorphisms are produced only as nonemptiness assertions, not as explicitly named maps.
--
--   This is the standard statement that two field extensions of a domain with injective structure maps can be amalgamated inside a single algebraically closed $D$-algebra. It serves as an infrastructure step used when comparing the residue field of a place, or a field of definition, with a fixed algebraically closed field; it is invoked in the computations of $j$-invariants of Tate-type points on modular curves and in the Drinfeld-type global argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_isAlgClosed_algHom_algHom_of_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem exists_isAlgClosed_algHom_algHom_of_injective
    (D : Type) [CommRing D] [IsDomain D]
    (E₁ E₂ : Type) [Field E₁] [Field E₂] [Algebra D E₁] [Algebra D E₂]
    (h₁ : Function.Injective (algebraMap D E₁)) (h₂ : Function.Injective (algebraMap D E₂)) :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : IsAlgClosed Ω') (_ : Algebra D Ω'),
      Nonempty (E₁ →ₐ[D] Ω') ∧ Nonempty (E₂ →ₐ[D] Ω') := by sorry
