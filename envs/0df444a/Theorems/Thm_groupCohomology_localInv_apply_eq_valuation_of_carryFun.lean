-- Prove2me | Theorems.Thm_groupCohomology_localInv_apply_eq_valuation_of_carryFun
-- name    : groupCohomology.localInv_apply_eq_valuation_of_carryFun
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/122123dc-1315-5cc5-823d-43a16d1e37f2
-- title:
--   Local invariant of unramified carry class is v_q(a) mod p
-- statement:
--   Fix a prime $p$ and a primitive $p$-th root of unity $\zeta$ in $\overline{\mathbb{Q}}$, and a prime $q$. Let $a \in \mathbb{Q}_q$ be non-zero, let $u$ be a unit of $\overline{\mathbb{Q}}_q$ (the field `PadicAlgCl q`) whose underlying element is the image $\iota_q(\zeta)$ of $\zeta$ under the embedding [`padicEmbedding q`](def/GaloisRep_CompletionBridge.html#L17) obtained by lifting $\mathbb{Q} \hookrightarrow \overline{\mathbb{Q}}_q$ along algebraic closedness, and let $L = \mathbb{Q}_q\bigl(\{x \in \overline{\mathbb{Q}}_q : x^{q^p-1} = 1\}\bigr)$. Let $\varphi$ be a $\mathbb{Q}_q$-automorphism of $L$ such that every automorphism of $L$ lies in the subgroup of integer powers of $\varphi$, such that $\varphi$ has finite order, and such that $\varphi(x) = x^{q}$ for every $x \in L$ with $x^{q^p-1} = 1$; assume further that $L$ is normal over $\mathbb{Q}_q$. Let $\alpha$ be a unit of $L$ whose underlying element is the image of $a$ in $\overline{\mathbb{Q}}_q$. Finally let $z$ be a $\mathbb{Z}/p$-valued function on pairs of elements of $\operatorname{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$ lying in `levelCocycles₂` for the homomorphism `primeLocalToGlobal q` (restriction of local automorphisms to $\overline{\mathbb{Q}}$) with coefficients in the one-dimensional representation `ofChar` attached to the mod-$p$ cyclotomic character `cycloChar p` composed with that homomorphism, i.e. the twist of the trivial line by that character. The last hypothesis requires that the difference of the cochain $(g,h) \mapsto u^{(z(g,h)).\mathrm{val}}$, read additively, and the inflation `unitsInflate₂` from $L^\times$ to $\overline{\mathbb{Q}}_q^\times$ of the carry cochain `carryFun φ` with value $\alpha$ — the cochain sending $(g,h)$ to $\alpha$ when $\operatorname{ord}(\varphi)$ is at most the sum of the exponents of $g$ and $h$ as powers of $\varphi$, and to $1$ otherwise — lies in `levelCoboundaries₂` for [`localGaloisToGlobal q`](def/GaloisRep_CompletionBridge.html#L41) with coefficients the Galois module $\overline{\mathbb{Q}}_q^\times$. The conclusion is that the $\mathbb{Z}/p$-linear form `localInv p ζ q` takes, on the class of $z$ in `continuousH2`, the value of the $q$-adic valuation of $a$ reduced modulo $p$.
--
--   This is the computation of the local invariant of the unramified cyclic algebra $(L/\mathbb{Q}_q, \varphi, a)$ with $L = \mathbb{Q}_q(\mu_{q^p-1})$: the normalisation built into `IsLocalInv` pins the invariant down for $a = q$, and the statement extends it to every non-zero $a \in \mathbb{Q}_q$, giving $v_q(a) \bmod p$. It is used in the local analysis of the classes attached to Kummer cocycles, notably by [`NumberField.PlaceDecomp.localInv_eq_of_inflate_eq_kummer`](thm.html#NumberField.PlaceDecomp.localInv_eq_of_inflate_eq_kummer) and [`groupCohomology.localInv_smul_kummerCocycle_eq_apply_frobenius_mul_valuation`](thm.html#groupCohomology.localInv_smul_kummerCocycle_eq_apply_frobenius_mul_valuation).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_localInv_apply_eq_valuation_of_carryFun.lean

import Mathlib
import Definitions.Def_GroupCohomology_LocalInvariant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory ExtCitation
open groupCohomology

theorem groupCohomology.localInv_apply_eq_valuation_of_carryFun
    (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : Nat.Primes) [Fact ((q : ℕ)).Prime]
    (a : ℚ_[q]) (ha : a ≠ 0)
    (u : (PadicAlgCl q)ˣ) (hu : (u : PadicAlgCl q) = padicEmbedding q ζ)
    (φ : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}) ≃ₐ[ℚ_[q]] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))
    (hs : ∀ σ, σ ∈ Subgroup.zpowers φ) (hfin : IsOfFinOrder φ)
    (hφ : ∀ x : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}), (x : PadicAlgCl q) ^ ((q : ℕ) ^ p - 1) = 1 → (φ x : PadicAlgCl q) = (x : PadicAlgCl q) ^ (q : ℕ))
    (α : ((IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))ˣ)
    (hα : ((α : (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) a)
    (_ : Normal ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1}))
    (z : primeLocalGaloisGroup q × primeLocalGaloisGroup q → ZMod p)
    (hz : z ∈ levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
    (hcob : (fun g : (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) => Additive.ofMul (u ^ (z g).val))
        - unitsInflate₂ (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})
            (carryFun φ hs hfin (A := Rep.ofAlgebraAutOnUnits ℚ_[q] (IntermediateField.adjoin ℚ_[q] {x : PadicAlgCl q | x ^ ((q : ℕ) ^ p - 1) = 1})) (Additive.ofMul α))
        ∈ levelCoboundaries₂ (localGaloisToGlobal q) (Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) :
    localInv p ζ q (continuousH2π (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))) ⟨z, hz⟩)
      = ((Padic.valuation a : ℤ) : ZMod p) := by sorry
