-- Prove2me | Theorems.Thm_groupCohomology_natCard_continuousClasses_ofChar_eq_natCard_units_quot
-- name    : groupCohomology.natCard_continuousClasses_ofChar_eq_natCard_units_quot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/6e7847e8-a181-5183-927a-7495a785884b
-- title:
--   Level-constant classes in H¹(χ) count K^×/(K^×)ᵖ
-- statement:
--   Let $K\subseteq L$ be fields with $L/K$ Galois, let $p$ be a prime, write $G=L\simeq_{\mathrm{alg}[K]}L$ for the group of $K$-algebra automorphisms of $L$, and let $\chi\colon G\to(\mathbb{Z}/p)^\times$ be a group homomorphism. Here `ofChar χ` denotes the one-dimensional representation of $G$ over $\mathbb{Z}/p$ given by $g\mapsto \chi(g)\cdot\mathrm{id}$, i.e. the trivial representation on $\mathbb{Z}/p$ twisted by $\chi$. Assume given $\zeta\in L^\times$, a primitive $p$-th root of unity, such that $g\cdot\zeta=\zeta^{(\chi g).\mathrm{val}}$ for every $g\in G$, and assume that every $a\in K^\times$ acquires a $p$-th root in $L^\times$, i.e. for each $a$ there is $\alpha\in L^\times$ with $\mathrm{algebraMap}_{K,L}(a)=\alpha^p$. Let `adm` be a $\mathbb{Z}/p$-submodule of $H^1(\mathrm{ofChar}\,\chi)$ whose elements are characterised as follows: $x\in$ `adm` if and only if $x$ is the image under the canonical projection `H1π` of some $1$-cocycle $c$ for which there exists an intermediate field $E$ of $L/K$, finite-dimensional over $K$, with $c(g s)=c(g)$ for all $g\in G$ and all $s$ in the fixing subgroup of $E$. Then the cardinality of `adm` equals the cardinality of $K^\times$ modulo the image of the $p$-th power homomorphism `powMonoidHom p` on $K^\times$, both computed as `Nat.card` (so the common value is $0$ if either side is infinite).
--
--   This is Kummer theory in the form adapted to the full (possibly infinite) Galois group: the subgroup of classes in $H^1(G,\mu_p)$ represented by a cocycle constant on cosets of $\mathrm{Gal}(L/E)$ for some finite subextension $E/K$ — the classes of finite level — is in bijection with $K^\times/(K^\times)^p$. It is used in the computation of the local terms entering the dual Selmer group estimate, being cited in the specialisation of this count to the cyclotomic character at a prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_natCard_continuousClasses_ofChar_eq_natCard_units_quot.lean

import Mathlib
import Definitions.Def_DualSelmer_ExtConditions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u
open CategoryTheory groupCohomology

theorem groupCohomology.natCard_continuousClasses_ofChar_eq_natCard_units_quot
    {K L : Type} [Field K] [Field L] [Algebra K L] [IsGalois K L] {p : ℕ} [Fact p.Prime]
    (χ : (L ≃ₐ[K] L) →* (ZMod p)ˣ) {ζ : Lˣ} (hζp : IsPrimitiveRoot ζ p)
    (hζ : ∀ g : L ≃ₐ[K] L, g • ζ = ζ ^ (χ g : ZMod p).val)
    (hroots : ∀ a : Kˣ, ∃ α : Lˣ, algebraMap K L (a : K) = (α : L) ^ p)
    (adm : Submodule (ZMod p) (H1 (ofChar χ)))
    (hadm : ∀ x, x ∈ adm ↔ ∃ c : cocycles₁ (ofChar χ),
      (∃ E : IntermediateField K L, FiniteDimensional K E ∧
        ∀ g s : L ≃ₐ[K] L, s ∈ E.fixingSubgroup → c.val (g * s) = c.val g) ∧ (H1π _).hom c = x) :
    Nat.card adm = Nat.card (Kˣ ⧸ (powMonoidHom p : Kˣ →* Kˣ).range) := by sorry
