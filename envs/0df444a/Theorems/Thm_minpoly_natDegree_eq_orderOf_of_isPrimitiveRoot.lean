-- Prove2me | Theorems.Thm_minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot
-- name    : minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/ddc30d96-a051-5cfc-bf09-133b459867b6
-- title:
--   Degree of a primitive m-th root of unity over a finite field
-- statement:
--   Let $F$ be a finite field and $E$ a field equipped with an $F$-algebra structure, let $m$ be a natural number and $\zeta \in E$ a primitive $m$-th root of unity (in the Mathlib sense: `IsPrimitiveRoot ζ m`), and assume that $m$ is coprime to $Q := \mathrm{card}(F)$. Writing $u$ for the unit of $\mathbb{Z}/m$ determined by the class of $Q$ together with this coprimality, the assertion is a conjunction of two statements. First, the degree of the minimal polynomial of $\zeta$ over $F$ equals the order of $u$ in $(\mathbb{Z}/m)^\times$, i.e. the multiplicative order of $Q$ modulo $m$. Second, for every $x \in E$ one has $\operatorname{aeval}_x(\operatorname{minpoly}_F \zeta) = 0$ if and only if $x = \zeta^{Q^i}$ for some natural number $i$; that is, the roots of the minimal polynomial of $\zeta$ lying in $E$ are exactly the elements of the Frobenius orbit $\{\zeta^{Q^i} : i \ge 0\}$ of $\zeta$.
--
--   This is the standard description of the irreducible factors of the $m$-th cyclotomic polynomial over a finite field: the residue degree of a primitive $m$-th root of unity is the order of the residue cardinality modulo $m$, and the conjugates of $\zeta$ are its Frobenius translates. It is used in the treatment of the unramified cyclotomic layers of local fields, in particular by [`ExtCitation.LocalLevel.exists_eq_pow_card_pow_of_mem_rootSet`](thm.html#ExtCitation.LocalLevel.exists_eq_pow_card_pow_of_mem_rootSet) and by [`IntermediateField.exists_norm_eq_adjoin_rootsOfUnity_padic`](thm.html#IntermediateField.exists_norm_eq_adjoin_rootsOfUnity_padic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial

theorem minpoly_natDegree_eq_orderOf_of_isPrimitiveRoot
    (F E : Type) [Field F] [Fintype F] [Field E] [Algebra F E] (m : ℕ) (ζ : E) (hζ : IsPrimitiveRoot ζ m)
    (hm : (Fintype.card F).Coprime m) :
    (minpoly F ζ).natDegree = orderOf (ZMod.unitOfCoprime (Fintype.card F) hm) ∧
    ∀ x : E, Polynomial.aeval x (minpoly F ζ) = 0 ↔ ∃ i : ℕ, x = ζ ^ (Fintype.card F ^ i) := by sorry
