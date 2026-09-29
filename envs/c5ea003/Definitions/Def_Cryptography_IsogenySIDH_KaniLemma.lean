-- Prove2me | Definitions.Def_Cryptography_IsogenySIDH_KaniLemma
-- name    : Cryptography_IsogenySIDH_KaniLemma
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T17:05:19.43986+00:00
-- url     : https://prove2.me/theorems/795151a4-a6e1-4981-8e7e-4421c9ef3cd0
-- title:
--   Aether Catalog definitions — Cryptography_IsogenySIDH_KaniLemma
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.IsogenySIDH.KaniLemma`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/IsogenySIDH/KaniLemma.lean by skeleton subtraction
import Mathlib
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

namespace Cryptography.SIDH

open Function

/-- An **isogeny diamond**: a commutative square of isogenies
`ψ' ∘ φ = φ' ∘ ψ` with `deg φ = deg φ' = a` and `deg ψ = deg ψ' = b`,
together with the four dual isogenies.

Curves are modelled by their groups of points and isogenies by group
homomorphisms; the degree relations `φ^ φ = [a] = φ φ^` are the defining
property of the dual isogeny. -/
structure Diamond (E₁ E₂ E₃ E₄ : Type*) [AddCommGroup E₁] [AddCommGroup E₂]
    [AddCommGroup E₃] [AddCommGroup E₄] where
  /-- The degree of the horizontal isogenies `φ`, `φ'`. -/
  a : ℕ
  /-- The degree of the vertical isogenies `ψ`, `ψ'`. -/
  b : ℕ
  /-- The secret horizontal isogeny `E₁ → E₂`. -/
  phi : E₁ →+ E₂
  /-- The vertical isogeny `E₁ → E₃`. -/
  psi : E₁ →+ E₃
  /-- The pushforward of `φ` along `ψ`. -/
  phi' : E₃ →+ E₄
  /-- The pushforward of `ψ` along `φ`. -/
  psi' : E₂ →+ E₄
  /-- The dual of `φ`. -/
  phiHat : E₂ →+ E₁
  /-- The dual of `ψ`. -/
  psiHat : E₃ →+ E₁
  /-- The dual of `φ'`. -/
  phi'Hat : E₄ →+ E₃
  /-- The dual of `ψ'`. -/
  psi'Hat : E₄ →+ E₂
  phiHat_phi : ∀ P, phiHat (phi P) = (a : ℤ) • P
  phi_phiHat : ∀ P, phi (phiHat P) = (a : ℤ) • P
  psiHat_psi : ∀ P, psiHat (psi P) = (b : ℤ) • P
  psi_psiHat : ∀ P, psi (psiHat P) = (b : ℤ) • P
  phi'Hat_phi' : ∀ P, phi'Hat (phi' P) = (a : ℤ) • P
  phi'_phi'Hat : ∀ P, phi' (phi'Hat P) = (a : ℤ) • P
  psi'Hat_psi' : ∀ P, psi'Hat (psi' P) = (b : ℤ) • P
  psi'_psi'Hat : ∀ P, psi' (psi'Hat P) = (b : ℤ) • P
  /-- The diamond commutes. -/
  square : ∀ P, psi' (phi P) = phi' (psi P)
  /-- Isogenies are surjective on geometric points. -/
  phi_surjective : Surjective phi
  psi_surjective : Surjective psi
  psi'_surjective : Surjective psi'

/-- The `n`-torsion subgroup `E[n]` of an abelian group. -/
def nTorsion (E : Type*) [AddCommGroup E] (n : ℕ) : AddSubgroup E where
  carrier := {x | (n : ℤ) • x = 0}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at *
    rw [smul_add, hx, hy, add_zero]
  zero_mem' := by simp
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq] at *
    rw [smul_neg, hx, neg_zero]


/-- If `n • x = 0` and `k ≡ 1 (mod n)` then `k • x = x`. -/
theorem zsmul_eq_self_of_one_add {E : Type*} [AddCommGroup E] {n k : ℤ} {x : E}
    (hx : n • x = 0) (hk : ∃ v : ℤ, k = 1 + n * v) : k • x = x := by
  obtain ⟨v, rfl⟩ := hk
  rw [add_smul, one_smul, mul_comm, mul_smul, hx, smul_zero, add_zero]

/-- The `n`-torsion of a product is the product of the `n`-torsions. -/
def nTorsionProdEquiv (A B : Type*) [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    nTorsion (A × B) n ≃+ nTorsion A n × nTorsion B n where
  toFun x := (⟨x.1.1, (Prod.ext_iff.mp x.2).1⟩, ⟨x.1.2, (Prod.ext_iff.mp x.2).2⟩)
  invFun y := ⟨(y.1.1, y.2.1), Prod.ext_iff.mpr ⟨y.1.2, y.2.2⟩⟩
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl
  map_add' x y := rfl


namespace Diamond

variable {E₁ E₂ E₃ E₄ : Type*} [AddCommGroup E₁] [AddCommGroup E₂]
    [AddCommGroup E₃] [AddCommGroup E₄] (D : Diamond E₁ E₂ E₃ E₄)

/-- The degree `N = a + b` of the associated `(N,N)`-isogeny. -/
def N : ℕ := D.a + D.b

/-! ### Coprimality bookkeeping -/

/-- If `a` and `b` are coprime then so are `a` and `N = a + b`. -/
theorem coprime_a_N (hab : Nat.Coprime D.a D.b) : Nat.Coprime D.a D.N := by
  show Nat.Coprime D.a (D.a + D.b)
  simp only [Nat.Coprime] at hab ⊢
  rw [Nat.gcd_comm, add_comm, Nat.gcd_add_self_left, Nat.gcd_comm]
  exact hab


/-- Bézout: `a` is invertible modulo `N = a + b` when `gcd(a,b) = 1`. -/
theorem exists_inv_a (hab : Nat.Coprime D.a D.b) :
    ∃ u v : ℤ, (D.a : ℤ) * u = 1 + (D.N : ℤ) * v := by
  obtain ⟨p, q, hpq⟩ := Nat.Coprime.isCoprime (D.coprime_a_N hab)
  exact ⟨p, -q, by linear_combination hpq⟩



/-! ### The two derived "dual square" identities -/

/-- Transporting the commutative square through the duals: `φ'^ ∘ ψ' = ψ ∘ φ^`.

This is the identity that makes the SIDH public torsion data usable: it says
that `ψ` is determined on the image of `φ^` by the pushforward `ψ'`. -/
theorem phi'Hat_psi' (Q : E₂) : D.phi'Hat (D.psi' Q) = D.psi (D.phiHat Q) := by
  obtain ⟨P, hP⟩ := D.phi_surjective Q
  rw [← hP]
  rw [D.square]
  rw [D.phi'Hat_phi']
  rw [D.phiHat_phi]
  simp

/-- The dual of the commutative square: `φ^ ∘ ψ'^ = ψ^ ∘ φ'^`. -/
theorem phiHat_psi'Hat (R : E₄) : D.phiHat (D.psi'Hat R) = D.psiHat (D.phi'Hat R) := by
  obtain ⟨Q, hQ⟩ := D.psi'_surjective R
  rw [← hQ, D.psi'Hat_psi', D.phiHat.map_zsmul, D.phi'Hat_psi', D.psiHat_psi]


/-! ### The Kani isogeny -/

/-- The **Kani isogeny** `F : E₁ × E₄ → E₂ × E₃` attached to a diamond,
given by the matrix `((φ, ψ'^), (-ψ, φ'^))`. -/
def kani : (E₁ × E₄) →+ (E₂ × E₃) :=
  AddMonoidHom.mk' (fun z => (D.phi z.1 + D.psi'Hat z.2, -D.psi z.1 + D.phi'Hat z.2))
    (by intro x y; simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk,
          Prod.mk.injEq, neg_add]; constructor <;> abel)

/-- The dual Kani isogeny `F^ : E₂ × E₃ → E₁ × E₄`, given by the transposed
matrix of duals `((φ^, -ψ^), (ψ', φ'))`. -/
def kaniDual : (E₂ × E₃) →+ (E₁ × E₄) :=
  AddMonoidHom.mk' (fun w => (D.phiHat w.1 - D.psiHat w.2, D.psi' w.1 + D.phi' w.2))
    (by intro x y; simp only [Prod.fst_add, Prod.snd_add, map_add, Prod.mk_add_mk,
          Prod.mk.injEq]; constructor <;> abel)

@[simp] theorem kani_apply (z : E₁ × E₄) :
    D.kani z = (D.phi z.1 + D.psi'Hat z.2, -D.psi z.1 + D.phi'Hat z.2) := rfl


/-- **Kani's lemma, multiplicative form.**  `F^ ∘ F = [N]` with `N = a + b`. -/
theorem kaniDual_kani (z : E₁ × E₄) : D.kaniDual (D.kani z) = (D.N : ℤ) • z := by
  have hN : (D.N : ℤ) = (D.a : ℤ) + (D.b : ℤ) := by simp [N]
  refine Prod.ext ?_ ?_
  · show D.phiHat (D.phi z.1 + D.psi'Hat z.2) - D.psiHat (-D.psi z.1 + D.phi'Hat z.2)
        = (D.N : ℤ) • z.1
    rw [map_add, map_add, map_neg, D.phiHat_phi, D.psiHat_psi, D.phiHat_psi'Hat, hN, add_zsmul]
    abel
  · show D.psi' (D.phi z.1 + D.psi'Hat z.2) + D.phi' (-D.psi z.1 + D.phi'Hat z.2)
        = (D.N : ℤ) • z.2
    rw [map_add, map_add, map_neg, D.square, D.psi'_psi'Hat, D.phi'_phi'Hat, hN, add_zsmul]
    abel



/-- The kernel of `F` is killed by `N`: `F` is an `(N,N)`-isogeny. -/
theorem N_smul_eq_zero_of_mem_ker {z : E₁ × E₄} (hz : D.kani z = 0) :
    (D.N : ℤ) • z = 0 := by
  rw [← D.kaniDual_kani, hz, map_zero]

/-! ### The kernel of the Kani isogeny -/

/-- The parametrisation `Q ↦ (φ^ Q, ψ' Q)` of the kernel of `F`. -/
def graphMap : E₂ →+ (E₁ × E₄) := (D.phiHat.prod D.psi')

@[simp] theorem graphMap_apply (Q : E₂) : D.graphMap Q = (D.phiHat Q, D.psi' Q) := rfl

/-- The graph of `E₂[N]` under `Q ↦ (φ^ Q, ψ' Q)` is contained in `ker F`. -/
theorem kani_graph {Q : E₂} (hQ : (D.N : ℤ) • Q = 0) : D.kani (D.graphMap Q) = 0 := by
  rw [kani_apply, graphMap_apply]
  rw [D.phi_phiHat Q, D.psi'Hat_psi' Q, D.phi'Hat_psi' Q]
  simp_all [N, add_smul]

/-- If `a` and `b` are coprime the graph parametrisation is injective; hence
the kernel of `F` has exactly as many points as `E₂[N]`. -/
theorem graphMap_injective (hab : Nat.Coprime D.a D.b) : Injective D.graphMap := by
  intro Q Q' h
  simp only [graphMap_apply, Prod.mk.injEq] at h
  have h1 : D.phiHat (Q - Q') = 0 := by simp [h.1]
  have h2 : D.psi' (Q - Q') = 0 := by simp [h.2]
  have hb : (D.b : ℤ) • (Q - Q') = 0 := by rw [← D.psi'Hat_psi']; simp [h2]
  have ha : (D.a : ℤ) • (Q - Q') = 0 := by rw [← D.phi_phiHat]; simp [h1]
  obtain ⟨x, y, hxy⟩ := Nat.Coprime.isCoprime hab
  have heq : (Q - Q') = (x * D.a + y * D.b : ℤ) • (Q - Q') := by simp [hxy]
  rw [add_smul, mul_zsmul, mul_zsmul, ha, hb] at heq
  simp at heq
  exact sub_eq_zero.mp heq

/-- **Kani's lemma.**  For coprime degrees, the kernel of the Kani isogeny is
*exactly* the graph `{ (φ^ Q, ψ' Q) : Q ∈ E₂[N] }`.

This is the statement exploited by the Castryck–Decru attack: the SIDH public
data (the images `ψ'` of the `N`-torsion, together with `φ^` on that torsion)
determines a subgroup of `E₁ × E₄` which is the kernel of an isogeny of smooth
degree `N²`, and hence can be computed. -/
theorem mem_ker_kani_iff (hab : Nat.Coprime D.a D.b) (z : E₁ × E₄) :
    D.kani z = 0 ↔ ∃ Q : E₂, (D.N : ℤ) • Q = 0 ∧ z = D.graphMap Q := by
  constructor
  · intro hz
    obtain ⟨u, v, huv⟩ := D.exists_inv_a hab
    obtain ⟨x, y⟩ := z
    have hz2 : -D.psi x + D.phi'Hat y = 0 := by simpa using congrArg Prod.snd hz
    have hN := D.N_smul_eq_zero_of_mem_ker hz
    have hNx : (D.N : ℤ) • x = 0 := by simpa using congrArg Prod.fst hN
    have hNy : (D.N : ℤ) • y = 0 := by simpa using congrArg Prod.snd hN
    have hpsi : D.psi x = D.phi'Hat y := by rwa [neg_add_eq_zero] at hz2
    refine ⟨u • D.phi x, ?_, ?_⟩
    · rw [smul_comm, ← map_zsmul, hNx, map_zero, smul_zero]
    · have hxx : D.phiHat (u • D.phi x) = x := by
        rw [map_zsmul, D.phiHat_phi, smul_smul, mul_comm u (D.a : ℤ)]
        exact zsmul_eq_self_of_one_add hNx ⟨v, huv⟩
      have hyy : D.psi' (u • D.phi x) = y := by
        rw [map_zsmul, D.square, hpsi, D.phi'_phi'Hat, smul_smul, mul_comm u (D.a : ℤ)]
        exact zsmul_eq_self_of_one_add hNy ⟨v, huv⟩
      rw [graphMap_apply, hxx, hyy]
  · rintro ⟨Q, hQ, rfl⟩
    exact D.kani_graph hQ

/-! ### The kernel does not split off either factor -/



/-! ### Degree of the shared secret -/



/-! ### `ker F` is isomorphic to `E₂[N]` -/

/-- The graph parametrisation, viewed as a map into the kernel of `F`. -/
def graphToKer : nTorsion E₂ D.N →+ D.kani.ker where
  toFun Q := ⟨D.graphMap Q.1, D.kani_graph Q.2⟩
  map_zero' := by ext <;> simp
  map_add' := by intro Q R; ext <;> simp

/-- **Degree of the Kani isogeny.**  For coprime degrees the kernel of `F` is
isomorphic to the full `N`-torsion of `E₂`; since `E₂[N] ≅ (ℤ/N)²` for an
elliptic curve, `F` is an isogeny of degree `N²`. -/
noncomputable def kerEquivTorsion (hab : Nat.Coprime D.a D.b) :
    nTorsion E₂ D.N ≃+ D.kani.ker :=
  AddEquiv.ofBijective D.graphToKer
    ⟨fun Q Q' h => Subtype.ext (D.graphMap_injective hab (congrArg Subtype.val h)), by
      rintro ⟨z, hz⟩
      obtain ⟨Q, hQ, rfl⟩ := (D.mem_ker_kani_iff hab z).mp (AddMonoidHom.mem_ker.mp hz)
      exact ⟨⟨Q, hQ⟩, rfl⟩⟩


/-! ### `ker F` is the graph of an isomorphism `E₁[N] ≃ E₄[N]` -/

/-- The explicit gluing map `x ↦ u • ψ'(φ x)`, for `u` an inverse of `a`
modulo `N`. -/
def glueMap (u : ℤ) : E₁ →+ E₄ :=
  AddMonoidHom.mk' (fun x => u • D.psi' (D.phi x)) (by intro x y; simp [smul_add])

/-- The explicit inverse gluing map `y ↦ w • φ^(ψ'^ y)`, for `w` an inverse of
`b` modulo `N`. -/
def unglueMap (w : ℤ) : E₄ →+ E₁ :=
  AddMonoidHom.mk' (fun y => w • D.phiHat (D.psi'Hat y)) (by intro x y; simp [smul_add])

@[simp] theorem glueMap_apply (u : ℤ) (x : E₁) : D.glueMap u x = u • D.psi' (D.phi x) := rfl


/-- The gluing map sends `N`-torsion to `N`-torsion. -/
theorem glueMap_mem_torsion (u : ℤ) {x : E₁} (hx : (D.N : ℤ) • x = 0) :
    (D.N : ℤ) • D.glueMap u x = 0 := by
  rw [glueMap_apply, smul_comm, ← map_zsmul, ← map_zsmul, ← map_zsmul, hx]
  simp








/-- The gluing map as a homomorphism `E₁[N] → E₄[N]`. -/
def glueTorsion (u : ℤ) : nTorsion E₁ D.N →+ nTorsion E₄ D.N where
  toFun x := ⟨D.glueMap u x.1, D.glueMap_mem_torsion u x.2⟩
  map_zero' := by ext; simp
  map_add' x y := by ext; simp



/-! ## A concrete isogeny diamond: complex multiplication by Gaussian integers

The theory above is not vacuous.  We exhibit an explicit diamond of coprime
degrees `a = 5`, `b = 2` modelled on the CM elliptic curve `E = ℂ/ℤ[i]`, whose
endomorphism ring is the Gaussian integers, with `deg [α] = N(α) = α ᾱ` and
dual `[α]^ = [ᾱ]`.  Its group of torsion points is `(ℚ/ℤ)²` with `ℤ[i]` acting
through the matrix `u + v i ↦ ((u, -v), (v, u))`. -/

/-- The group `ℚ/ℤ`, the torsion of a one–dimensional complex torus. -/
abbrev QZ := ℚ ⧸ AddSubgroup.zmultiples (1 : ℚ)

/-- `ℚ/ℤ` is divisible. -/
theorem QZ_divisible {d : ℤ} (hd : d ≠ 0) (x : QZ) : ∃ y : QZ, d • y = x := by
  induction x using Quotient.inductionOn
  case h a =>
    refine ⟨Quotient.mk _ (a / d), ?_⟩
    have key : (d : ℤ) • (a / d : ℚ) = a := by simp [zsmul_eq_mul, mul_div_cancel₀, hd]
    apply Quotient.eq.mpr
    simp [key]

/-- The homomorphism `ℤ → ℚ/ℤ`, `k ↦ k/n`, whose image is the `n`-torsion. -/
noncomputable def QZfrac (n : ℕ) : ℤ →+ QZ :=
  (QuotientAddGroup.mk' (AddSubgroup.zmultiples (1 : ℚ))).comp
    (zmultiplesHom ℚ ((n : ℚ)⁻¹))





/-- Multiplication by the Gaussian integer `u + v i` on `(ℚ/ℤ)² = ℂ/ℤ[i]`
(torsion), i.e. the endomorphism with matrix `((u, -v), (v, u))`. -/
noncomputable def gaussHom (u v : ℤ) : QZ × QZ →+ QZ × QZ :=
  AddMonoidHom.mk' (fun p => (u • p.1 - v • p.2, v • p.1 + u • p.2))
    (by intro p q; simp only [Prod.fst_add, Prod.snd_add, smul_add, Prod.mk_add_mk,
          Prod.mk.injEq]; constructor <;> abel)


@[simp] theorem gaussHom_apply (u v : ℤ) (p : QZ × QZ) :
    gaussHom u v p = (u • p.1 - v • p.2, v • p.1 + u • p.2) := rfl

/-- Multiplication by Gaussian integers is multiplicative: `[z] ∘ [z'] = [z z']`. -/
theorem gaussHom_comp (u v u' v' : ℤ) (p : QZ × QZ) :
    gaussHom u v (gaussHom u' v' p) = gaussHom (u * u' - v * v') (u * v' + v * u') p := by
  simp only [gaussHom_apply]
  refine Prod.ext ?_ ?_ <;>
    simp_rw [smul_sub, smul_add, smul_smul, add_smul, sub_smul] <;> abel

/-- `[ᾱ] ∘ [α] = [N(α)]`: the norm relation defining the dual isogeny. -/
theorem gaussHom_conj (u v : ℤ) (p : QZ × QZ) :
    gaussHom u (-v) (gaussHom u v p) = (u ^ 2 + v ^ 2 : ℤ) • p := by
  rw [gaussHom_comp, show u * u - -v * v = u ^ 2 + v ^ 2 by ring,
    show u * v + -v * u = 0 by ring]
  simp [gaussHom, Prod.ext_iff]

/-- A nonzero Gaussian integer acts surjectively on the divisible group
`(ℚ/ℤ)²`. -/
theorem gaussHom_surjective {u v : ℤ} (h : u ^ 2 + v ^ 2 ≠ 0) :
    Function.Surjective (gaussHom u v) := by
  intro w
  obtain ⟨q1, hq1⟩ := QZ_divisible h w.1
  obtain ⟨q2, hq2⟩ := QZ_divisible h w.2
  refine ⟨gaussHom u (-v) (q1, q2), ?_⟩
  have hconj := gaussHom_conj u (-v) (q1, q2)
  rw [neg_neg, neg_sq] at hconj
  rw [hconj]
  exact Prod.ext hq1 hq2

/-- `gaussHom` is additive in the Gaussian integer. -/
theorem gaussHom_add (u v u' v' : ℤ) (p : QZ × QZ) :
    gaussHom (u + u') (v + v') p = gaussHom u v p + gaussHom u' v' p := by
  simp only [gaussHom_apply, add_smul, Prod.mk_add_mk, Prod.mk.injEq]
  constructor <;> abel

/-- `gaussHom 1 0` is the identity. -/
theorem gaussHom_one (p : QZ × QZ) : gaussHom 1 0 p = p := by
  simp [gaussHom]

/-- An explicit isogeny diamond with coprime degrees `a = 5` (multiplication by
`1 + 2i`) and `b = 2` (multiplication by `1 + i`) on the CM torus `ℂ/ℤ[i]`. -/
noncomputable def cmDiamond : Diamond (QZ × QZ) (QZ × QZ) (QZ × QZ) (QZ × QZ) where
  a := 5
  b := 2
  phi := gaussHom 1 2
  psi := gaussHom 1 1
  phi' := gaussHom 1 2
  psi' := gaussHom 1 1
  phiHat := gaussHom 1 (-2)
  psiHat := gaussHom 1 (-1)
  phi'Hat := gaussHom 1 (-2)
  psi'Hat := gaussHom 1 (-1)
  phiHat_phi P := by simpa using gaussHom_conj 1 2 P
  phi_phiHat P := by simpa using gaussHom_conj 1 (-2) P
  psiHat_psi P := by simpa using gaussHom_conj 1 1 P
  psi_psiHat P := by simpa using gaussHom_conj 1 (-1) P
  phi'Hat_phi' P := by simpa using gaussHom_conj 1 2 P
  phi'_phi'Hat P := by simpa using gaussHom_conj 1 (-2) P
  psi'Hat_psi' P := by simpa using gaussHom_conj 1 1 P
  psi'_psi'Hat P := by simpa using gaussHom_conj 1 (-1) P
  square P := by rw [gaussHom_comp, gaussHom_comp]; norm_num
  phi_surjective := gaussHom_surjective (by norm_num)
  psi_surjective := gaussHom_surjective (by norm_num)
  psi'_surjective := gaussHom_surjective (by norm_num)




/-- Compatibility of `gaussHom` with multiplication of Gaussian integers. -/
theorem gaussHom_mul_apply (z w : GaussianInt) (p : QZ × QZ) :
    gaussHom (z * w).re (z * w).im p = gaussHom z.re z.im (gaussHom w.re w.im p) := by
  rw [gaussHom_comp]
  simp [sub_eq_add_neg]

/-- Compatibility of `gaussHom` with addition of Gaussian integers. -/
theorem gaussHom_add_apply (z w : GaussianInt) (p : QZ × QZ) :
    gaussHom (z + w).re (z + w).im p = gaussHom z.re z.im p + gaussHom w.re w.im p := by
  simpa using gaussHom_add z.re z.im w.re w.im p

/-- The zero Gaussian integer acts as zero. -/
theorem gaussHom_zero (p : QZ × QZ) : gaussHom 0 0 p = 0 := by
  simp [gaussHom]

/-- **Complex multiplication.**  The Gaussian integers embed in the
endomorphism ring of the torsion group of `ℂ/ℤ[i]`. -/
noncomputable def gaussEnd : GaussianInt →+* AddMonoid.End (QZ × QZ) where
  toFun z := gaussHom z.re z.im
  map_one' := by exact AddMonoidHom.ext fun p => gaussHom_one p
  map_mul' z w := by exact AddMonoidHom.ext fun p => gaussHom_mul_apply z w p
  map_zero' := by exact AddMonoidHom.ext fun p => gaussHom_zero p
  map_add' z w := by exact AddMonoidHom.ext fun p => gaussHom_add_apply z w p







end Diamond

end Cryptography.SIDH


