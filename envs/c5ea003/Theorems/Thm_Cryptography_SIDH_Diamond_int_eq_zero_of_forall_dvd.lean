-- Prove2me | Theorems.Thm_Cryptography_SIDH_Diamond_int_eq_zero_of_forall_dvd
-- name    : Cryptography.SIDH.Diamond.int_eq_zero_of_forall_dvd
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-17T20:22:20.866099+00:00
-- url     : https://prove2.me/theorems/7e97cac7-436b-4a23-9576-ec1c4af781ae
-- title:
--   An integer divisible by every positive integer is zero.
-- statement:
--   An integer divisible by every positive integer is zero.
--
--   ```lean
--   theorem Cryptography.SIDH.Diamond.int_eq_zero_of_forall_dvd{w : ℤ} (h : ∀ m : ℕ, 0 < m → ((m : ℤ) ∣ w)) :
--       w = 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Cryptography/IsogenySIDH/KaniLemma.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Cryptography/IsogenySIDH/KaniLemma.lean#L753

-- Thm stub generated from Cryptography/IsogenySIDH/KaniLemma.lean
import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_KaniLemma
/-
# Kani's lemma for SIDH isogeny diamonds

This file formalizes the algebraic core of *Kani's lemma*, the statement that
turns an "isogeny diamond"

```
        φ
   E₁ ------> E₂
   |          |
 ψ |          | ψ'
   v    φ'    v
   E₃ ------> E₄
```

with `deg φ = deg φ' = a`, `deg ψ = deg ψ' = b` and `ψ' ∘ φ = φ' ∘ ψ`, into a
single isogeny

`F = ( φ    ψ'^ )  :  E₁ × E₄ → E₂ × E₃`
`    (-ψ    φ'^ )`

of degree `N² = (a+b)²` between abelian surfaces, whose kernel is the graph
`{ (φ^ Q, ψ' Q) : Q ∈ E₂[N] }`.

Kani's lemma is exactly the engine of the Castryck–Decru–Maino–Martindale
attack on SIDH: the public torsion images of an SIDH key exchange determine the
subgroup `{ (φ^ Q, ψ' Q) }`, hence the isogeny `F` of *smooth* degree `N²`,
which can be computed and which exposes the secret isogeny `φ`.

## Formalization choices

We work with an abstract, self-contained model of the situation.  Curves are
modelled by their groups of geometric points (arbitrary additive commutative
groups), isogenies by group homomorphisms, and the dual isogenies are supplied
as data satisfying the two defining relations `φ^ ∘ φ = [deg φ]` and
`φ ∘ φ^ = [deg φ]`.  Surjectivity of an isogeny over an algebraically closed
field is recorded as a hypothesis for the three maps where it is needed.

Everything else - in particular the two "dual square" identities
`φ'^ ∘ ψ' = ψ ∘ φ^` and `φ^ ∘ ψ'^ = ψ^ ∘ φ'^` - is *derived*.

## Main results

* `SIDH.Diamond.kaniDual_kani`  : `F^ ∘ F = [N]`
* `SIDH.Diamond.kani_kaniDual`  : `F ∘ F^ = [N]`
* `SIDH.Diamond.kani_graph`     : the graph of `E₂[N]` lies in `ker F`
* `SIDH.Diamond.mem_ker_kani_iff` : `ker F` *equals* that graph (Kani's lemma)
* `SIDH.Diamond.ker_kani_eq_map` : subgroup form of the same statement
* `SIDH.Diamond.graphMap_injective` : the graph parametrisation is injective
* `SIDH.Diamond.kani_ker_inter_left/right` : `ker F` meets neither factor
* `SIDH.Diamond.kerEquivTorsion` : `ker F ≃+ E₂[N]`, and
  `SIDH.Diamond.card_ker_kani` : `#ker F = N²` once `#E₂[N] = N²`
* `SIDH.Diamond.exists_unique_partner_left/right`,
  `SIDH.Diamond.glueTorsion_bijective` : `ker F` is the graph of an isomorphism
  `E₁[N] ≃ E₄[N]`, explicitly `x ↦ u • ψ'(φ x)` with `a u ≡ 1 (mod N)`
* `SIDH.Diamond.smul_glueMap` : the secret action `ψ' ∘ φ` on the `N`-torsion is
  recovered from `ker F`, which is the structural content of the attack
* `SIDH.Diamond.cmDiamond` : an explicit diamond of degrees `5` and `2` coming
  from complex multiplication by `ℤ[i]`, so the theory is non-vacuous
* `SIDH.Diamond.card_nTorsion_QZ` : `#(ℚ/ℤ)[n] = n`, proved from the exact
  sequence `0 → nℤ → ℤ → (ℚ/ℤ)[n] → 0` given by `k ↦ k/n`
* `SIDH.Diamond.cmDiamond_card_ker` : the Kani isogeny of the concrete diamond
  has kernel of order `N² = 49`, the predicted degree
* `SIDH.Diamond.gaussEnd_injective` : the complex multiplication action of
  `ℤ[i]` on the torsion group `(ℚ/ℤ)²` is faithful
-/

open Cryptography.SIDH

-- open removed: section is not a namespace







open Diamond

variable {E₁ E₂ E₃ E₄ : Type*} [AddCommGroup E₁] [AddCommGroup E₂]
    [AddCommGroup E₃] [AddCommGroup E₄] (D : Diamond E₁ E₂ E₃ E₄)


/-! ### Coprimality bookkeeping -/






/-! ### The two derived "dual square" identities -/




/-! ### The Kani isogeny -/









/-! ### The kernel of the Kani isogeny -/






/-! ### The kernel does not split off either factor -/



/-! ### Degree of the shared secret -/



/-! ### `ker F` is isomorphic to `E₂[N]` -/




/-! ### `ker F` is the graph of an isomorphism `E₁[N] ≃ E₄[N]` -/
















/-! ## A concrete isogeny diamond: complex multiplication by Gaussian integers

The theory above is not vacuous.  We exhibit an explicit diamond of coprime
degrees `a = 5`, `b = 2` modelled on the CM elliptic curve `E = ℂ/ℤ[i]`, whose
endomorphism ring is the Gaussian integers, with `deg [α] = N(α) = α ᾱ` and
dual `[α]^ = [ᾱ]`.  Its group of torsion points is `(ℚ/ℤ)²` with `ℤ[i]` acting
through the matrix `u + v i ↦ ((u, -v), (v, u))`. -/

theorem Cryptography.SIDH.Diamond.int_eq_zero_of_forall_dvd{w : ℤ} (h : ∀ m : ℕ, 0 < m → ((m : ℤ) ∣ w)) :
    w = 0 := by sorry
