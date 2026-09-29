-- Prove2me | solution 2 for Cryptography.SIDH.Diamond.gaussEnd_injective
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T17:32:34.411619+00:00
-- url     : https://prove2.me/submissions/ef148fa8-3e59-4b9f-be11-00ba4b5969c5

import Mathlib
import Definitions.Def_Cryptography_IsogenySIDH_KaniLemma

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Cryptography/IsogenySIDH/KaniLemma.lean ====
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

-- [dropped: platform already declares Diamond]
-- [dropped: platform already declares nTorsion]
@[simp] theorem mem_nTorsion {E : Type*} [AddCommGroup E] {n : ℕ} {x : E} :
    x ∈ nTorsion E n ↔ (n : ℤ) • x = 0 := Iff.rfl

-- [dropped: platform already declares zsmul_eq_self_of_one_add]
-- [dropped: platform already declares nTorsionProdEquiv]
/-- Cardinality of the `n`-torsion of a product. -/
theorem card_nTorsion_prod (A B : Type*) [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    Nat.card (nTorsion (A × B) n) = Nat.card (nTorsion A n) * Nat.card (nTorsion B n) := by
  rw [Nat.card_congr (nTorsionProdEquiv A B n).toEquiv, Nat.card_prod]

namespace Diamond

variable {E₁ E₂ E₃ E₄ : Type*} [AddCommGroup E₁] [AddCommGroup E₂]
    [AddCommGroup E₃] [AddCommGroup E₄] (D : Diamond E₁ E₂ E₃ E₄)

-- [dropped: platform already declares N]
-- [dropped: platform already declares coprime_a_N]
/-- If `a` and `b` are coprime then so are `b` and `N = a + b`. -/
theorem coprime_b_N (hab : Nat.Coprime D.a D.b) : Nat.Coprime D.b D.N := by
  simp only [N, Nat.Coprime] at hab ⊢
  rw [Nat.gcd_add_self_right, Nat.gcd_comm]
  exact hab

-- [dropped: platform already declares exists_inv_a]
/-- Bézout: `b` is invertible modulo `N = a + b` when `gcd(a,b) = 1`. -/
theorem exists_inv_b (hab : Nat.Coprime D.a D.b) :
    ∃ w v : ℤ, (D.b : ℤ) * w = 1 + (D.N : ℤ) * v := by
  obtain ⟨p, q, hpq⟩ := Nat.Coprime.isCoprime (D.coprime_b_N hab)
  exact ⟨p, -q, by linear_combination hpq⟩


/-! ### The two derived "dual square" identities -/

-- [dropped: platform already declares phi'Hat_psi']
-- [dropped: platform already declares phiHat_psi'Hat]
/-- The remaining dual identity `ψ'^ ∘ φ' = φ ∘ ψ^`. -/
theorem psi'Hat_phi' (R : E₃) : D.psi'Hat (D.phi' R) = D.phi (D.psiHat R) := by
  obtain ⟨P, hP⟩ := D.psi_surjective R
  rw [← hP, ← D.square P, D.psiHat_psi]
  simp only [map_zsmul]
  rw [D.psi'Hat_psi']

/-! ### The Kani isogeny -/

-- [dropped: platform already declares kani]
-- [dropped: platform already declares kaniDual]
-- [dropped: platform already declares kani_apply]
@[simp] theorem kaniDual_apply (w : E₂ × E₃) :
    D.kaniDual w = (D.phiHat w.1 - D.psiHat w.2, D.psi' w.1 + D.phi' w.2) := rfl

-- [dropped: platform already declares kaniDual_kani]
/-- **Kani's lemma, multiplicative form (other side).**  `F ∘ F^ = [N]`. -/
theorem kani_kaniDual (w : E₂ × E₃) : D.kani (D.kaniDual w) = (D.N : ℤ) • w := by
  have hN : (D.N : ℤ) = (D.a : ℤ) + (D.b : ℤ) := by simp [N]
  refine Prod.ext ?_ ?_
  · show D.phi (D.phiHat w.1 - D.psiHat w.2) + D.psi'Hat (D.psi' w.1 + D.phi' w.2)
        = (D.N : ℤ) • w.1
    rw [map_sub, map_add, D.phi_phiHat, D.psi'Hat_psi', D.psi'Hat_phi', hN, add_zsmul]
    abel
  · show -D.psi (D.phiHat w.1 - D.psiHat w.2) + D.phi'Hat (D.psi' w.1 + D.phi' w.2)
        = (D.N : ℤ) • w.2
    rw [map_sub, map_add, D.psi_psiHat, D.phi'Hat_phi', D.phi'Hat_psi', hN, add_zsmul]
    abel

/-- `F` is surjective: an immediate consequence of `F ∘ F^ = [N]` is that
`N • (E₂ × E₃)` lies in the image of `F`. -/
theorem nsmul_mem_range_kani (w : E₂ × E₃) : ∃ z, D.kani z = (D.N : ℤ) • w :=
  ⟨D.kaniDual w, D.kani_kaniDual w⟩

-- [dropped: platform already declares N_smul_eq_zero_of_mem_ker]
-- [dropped: platform already declares graphMap]
-- [dropped: platform already declares graphMap_apply]
-- [dropped: platform already declares kani_graph]
-- [dropped: platform already declares graphMap_injective]
-- [dropped: platform already declares mem_ker_kani_iff]
/-- `ker F` meets `E₁ × 0` trivially. -/
theorem kani_ker_inter_left (hab : Nat.Coprime D.a D.b) {x : E₁}
    (hx : D.kani (x, 0) = 0) : x = 0 := by
  rw [kani_apply] at hx
  simp at hx
  have hphi : D.phi x = 0 := by simpa using hx.1
  have hpsi : D.psi x = 0 := by simpa using hx.2
  have ha : (D.a : ℤ) • x = 0 := by simp [← D.phiHat_phi, hphi]
  have hb : (D.b : ℤ) • x = 0 := by simp [← D.psiHat_psi, hpsi]
  obtain ⟨u, v, huv⟩ := Nat.Coprime.isCoprime hab
  rw [show x = (1 : ℤ) • x by simp, show (1 : ℤ) = u * (D.a : ℤ) + v * (D.b : ℤ) by rw [huv],
    add_zsmul, mul_zsmul, mul_zsmul]
  simp [ha, hb]

/-- `ker F` meets `0 × E₄` trivially. -/
theorem kani_ker_inter_right (hab : Nat.Coprime D.a D.b) {y : E₄}
    (hy : D.kani (0, y) = 0) : y = 0 := by
  rw [kani_apply] at hy
  simp at hy
  have h1 : D.psi'Hat y = 0 := by simpa using hy.1
  have h2 : D.phi'Hat y = 0 := by simpa using hy.2
  have ha : (D.a : ℤ) • y = 0 := by simp [← D.phi'_phi'Hat, h2]
  have hb : (D.b : ℤ) • y = 0 := by simp [← D.psi'_psi'Hat, h1]
  obtain ⟨u, v, huv⟩ := Nat.Coprime.isCoprime hab
  rw [show y = (1 : ℤ) • y by simp, show (1 : ℤ) = u * (D.a : ℤ) + v * (D.b : ℤ) by rw [huv],
    add_zsmul, mul_zsmul, mul_zsmul]
  simp [ha, hb]

/-! ### Degree of the shared secret -/

/-- The SIDH shared-secret isogeny `ψ' ∘ φ = φ' ∘ ψ : E₁ → E₄` has degree
`a * b`, in the sense that composing with its dual gives `[a*b]`. -/
theorem shared_degree (P : E₁) :
    D.phiHat (D.psi'Hat (D.psi' (D.phi P))) = ((D.a * D.b : ℕ) : ℤ) • P := by
  -- phiHat (psi'Hat (psi' (phi P)))
  -- = psiHat (phi'Hat (psi' (phi P)))  using phiHat_psi'Hat
  rw [D.phiHat_psi'Hat]
  -- = psiHat (psi (phiHat (phi P)))    using phi'Hat_psi'
  rw [D.phi'Hat_psi']
  -- = psiHat (psi (a • P))             using phiHat_phi
  rw [D.phiHat_phi]
  -- = psiHat (a • psi P)               homomorphism property
  rw [map_zsmul]
  -- = a • psiHat (psi P)               homomorphism property
  rw [map_zsmul]
  -- = a • (b • P)                      using psiHat_psi
  rw [D.psiHat_psi]
  -- = (a * b) • P
  rw [Nat.cast_mul, smul_smul]

/-- Both parties of the SIDH exchange compute the same isogeny to the shared
curve; in particular the two composite maps have the same kernel. -/
theorem shared_ker_eq :
    ((D.psi'.comp D.phi).ker) = ((D.phi'.comp D.psi).ker) := by
  congr 1
  ext P
  exact D.square P

/-! ### `ker F` is isomorphic to `E₂[N]` -/

-- [dropped: platform already declares graphToKer]
-- [dropped: platform already declares kerEquivTorsion]
/-- The kernel of the Kani isogeny has exactly `N²` points, given that the
`N`-torsion of an elliptic curve has `N²` points. -/
theorem card_ker_kani (hab : Nat.Coprime D.a D.b)
    (hcard : Nat.card (nTorsion E₂ D.N) = D.N ^ 2) :
    Nat.card D.kani.ker = D.N ^ 2 := by
  rw [← hcard]
  exact Nat.card_congr (kerEquivTorsion D hab).symm

/-! ### `ker F` is the graph of an isomorphism `E₁[N] ≃ E₄[N]` -/

-- [dropped: platform already declares glueMap]
-- [dropped: platform already declares unglueMap]
-- [dropped: platform already declares glueMap_apply]
@[simp] theorem unglueMap_apply (w : ℤ) (y : E₄) :
    D.unglueMap w y = w • D.phiHat (D.psi'Hat y) := rfl

-- [dropped: platform already declares glueMap_mem_torsion]
/-- The inverse gluing map sends `N`-torsion to `N`-torsion. -/
theorem unglueMap_mem_torsion (w : ℤ) {y : E₄} (hy : (D.N : ℤ) • y = 0) :
    (D.N : ℤ) • D.unglueMap w y = 0 := by
  rw [unglueMap_apply, smul_comm, ← map_zsmul, ← map_zsmul, ← map_zsmul, hy]
  simp

/-- **The kernel of `F` is a graph over `E₁[N]`**: for `u` inverse to `a` mod
`N`, every `N`-torsion point `x` of `E₁` is glued to `u • ψ'(φ x)`. -/
theorem glueMap_mem_ker {u : ℤ}
    (hu : ∃ v : ℤ, (D.a : ℤ) * u = 1 + (D.N : ℤ) * v) {x : E₁} (hx : (D.N : ℤ) • x = 0) :
    D.kani (x, D.glueMap u x) = 0 := by
  obtain ⟨v, hv⟩ := hu
  have hQ : (D.N : ℤ) • (u • D.phi x) = 0 := by
    rw [smul_comm, ← map_zsmul, hx, map_zero, smul_zero]
  have hx' : D.phiHat (u • D.phi x) = x := by
    rw [map_zsmul, D.phiHat_phi, smul_smul, mul_comm u (D.a : ℤ), hv, add_smul, one_smul, mul_comm (D.N : ℤ) v,
      mul_smul, hx, smul_zero, add_zero]
  have h := D.kani_graph hQ
  rw [graphMap_apply, hx', map_zsmul] at h
  exact h

/-- The two gluing maps are mutually inverse on the `N`-torsion. -/
theorem unglueMap_glueMap {u w : ℤ} (hu : ∃ v : ℤ, (D.a : ℤ) * u = 1 + (D.N : ℤ) * v)
    (hw : ∃ v : ℤ, (D.b : ℤ) * w = 1 + (D.N : ℤ) * v) {x : E₁} (hx : (D.N : ℤ) • x = 0) :
    D.unglueMap w (D.glueMap u x) = x := by
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := hw
  rw [unglueMap_apply, glueMap_apply, map_zsmul, D.psi'Hat_psi', map_zsmul, map_zsmul,
    D.phiHat_phi, smul_smul, smul_smul, smul_smul]
  refine zsmul_eq_self_of_one_add hx ⟨v + v' + (D.N : ℤ) * v * v', ?_⟩
  linear_combination ((D.b : ℤ) * w) * hv + (1 + (D.N : ℤ) * v) * hv'

/-- **The attack recovers the secret action from the kernel.**  On the
`N`-torsion, `a` times the gluing map (which is read off from `ker F`) is the
composite `ψ' ∘ φ`; since `a` is invertible modulo `N`, knowledge of `ker F` is
equivalent to knowledge of the secret isogeny on the `N`-torsion. -/
theorem smul_glueMap {u : ℤ} (hu : ∃ v : ℤ, (D.a : ℤ) * u = 1 + (D.N : ℤ) * v)
    {x : E₁} (hx : (D.N : ℤ) • x = 0) :
    (D.a : ℤ) • D.glueMap u x = D.psi' (D.phi x) := by
  obtain ⟨v, hv⟩ := hu
  have hz : (D.N : ℤ) • D.psi' (D.phi x) = 0 := by
    rw [← map_zsmul, ← map_zsmul, hx, map_zero, map_zero]
  rw [glueMap_apply, smul_smul, hv, add_smul, one_smul, mul_comm (D.N : ℤ) v, mul_smul, hz,
    smul_zero, add_zero]

/-- Every `N`-torsion point of `E₁` has a unique partner in `E₄` inside the
kernel of `F`. -/
theorem exists_unique_partner_left (hab : Nat.Coprime D.a D.b) {x : E₁}
    (hx : (D.N : ℤ) • x = 0) : ∃! y : E₄, D.kani (x, y) = 0 := by
  obtain ⟨u, v, huv⟩ := D.exists_inv_a hab
  refine ⟨D.glueMap u x, D.glueMap_mem_ker ⟨v, huv⟩ hx, fun y hy => ?_⟩
  have h0 : D.kani (0, y - D.glueMap u x) = 0 := by
    have : D.kani (0, y - D.glueMap u x)
        = D.kani (x, y) - D.kani (x, D.glueMap u x) := by
      rw [← map_sub]
      congr 1
      simp
    rw [this, hy, D.glueMap_mem_ker ⟨v, huv⟩ hx, sub_zero]
  have := D.kani_ker_inter_right hab h0
  exact sub_eq_zero.mp this

/-- Every `N`-torsion point of `E₄` has a unique partner in `E₁` inside the
kernel of `F`. -/
theorem exists_unique_partner_right (hab : Nat.Coprime D.a D.b) {y : E₄}
    (hy : (D.N : ℤ) • y = 0) : ∃! x : E₁, D.kani (x, y) = 0 := by
  obtain ⟨w, v, hwv⟩ := D.exists_inv_b hab
  have hQ : (D.N : ℤ) • (w • D.psi'Hat y) = 0 := by
    rw [smul_comm, ← map_zsmul, hy, map_zero, smul_zero]
  have hy' : D.psi' (w • D.psi'Hat y) = y := by
    rw [map_zsmul, D.psi'_psi'Hat, smul_smul, mul_comm w (D.b : ℤ)]
    exact zsmul_eq_self_of_one_add hy ⟨v, hwv⟩
  have hker : D.kani (D.unglueMap w y, y) = 0 := by
    have h := D.kani_graph hQ
    rw [graphMap_apply, hy', map_zsmul] at h
    exact h
  refine ⟨D.unglueMap w y, hker, fun x hx => ?_⟩
  have h0 : D.kani (x - D.unglueMap w y, 0) = 0 := by
    have : D.kani (x - D.unglueMap w y, 0)
        = D.kani (x, y) - D.kani (D.unglueMap w y, y) := by
      rw [← map_sub]
      congr 1
      simp
    rw [this, hx, hker, sub_zero]
  have := D.kani_ker_inter_left hab h0
  exact sub_eq_zero.mp this

/-- Subgroup form of Kani's lemma: `ker F` is the image of `E₂[N]` under the
graph parametrisation. -/
theorem ker_kani_eq_map (hab : Nat.Coprime D.a D.b) :
    D.kani.ker = (nTorsion E₂ D.N).map D.graphMap := by
  ext z
  simp only [AddMonoidHom.mem_ker, AddSubgroup.mem_map, mem_nTorsion,
    D.mem_ker_kani_iff hab, eq_comm]

-- [dropped: platform already declares glueTorsion]
@[simp] theorem glueTorsion_coe (u : ℤ) (x : nTorsion E₁ D.N) :
    (D.glueTorsion u x : E₄) = D.glueMap u x.1 := rfl

/-- **`ker F` is the graph of an isomorphism `E₁[N] ≃ E₄[N]`.**  This is the
form of Kani's lemma used to glue the two curves of an SIDH instance into a
single abelian surface. -/
theorem glueTorsion_bijective (hab : Nat.Coprime D.a D.b) {u : ℤ}
    (hu : ∃ v : ℤ, (D.a : ℤ) * u = 1 + (D.N : ℤ) * v) :
    Function.Bijective (D.glueTorsion u) := by
  constructor
  · intro x x' h
    have h1 : D.kani (x.1, D.glueMap u x.1) = 0 := D.glueMap_mem_ker hu x.2
    have h2 : D.kani (x'.1, D.glueMap u x'.1) = 0 := D.glueMap_mem_ker hu x'.2
    have hval : D.glueMap u x.1 = D.glueMap u x'.1 := congrArg Subtype.val h
    have hy : (D.N : ℤ) • D.glueMap u x.1 = 0 := D.glueMap_mem_torsion u x.2
    have h2' : D.kani (x'.1, D.glueMap u x.1) = 0 := by rw [hval]; exact h2
    exact Subtype.ext ((D.exists_unique_partner_right hab hy).unique h1 h2')
  · rintro ⟨y, hy⟩
    obtain ⟨x, hx, -⟩ := D.exists_unique_partner_right hab hy
    have hxT : (D.N : ℤ) • x = 0 := by
      simpa using congrArg Prod.fst (D.N_smul_eq_zero_of_mem_ker hx)
    exact ⟨⟨x, hxT⟩, Subtype.ext ((D.exists_unique_partner_left hab hxT).unique
      (D.glueMap_mem_ker hu hxT) hx)⟩

/-! ## A concrete isogeny diamond: complex multiplication by Gaussian integers

The theory above is not vacuous.  We exhibit an explicit diamond of coprime
degrees `a = 5`, `b = 2` modelled on the CM elliptic curve `E = ℂ/ℤ[i]`, whose
endomorphism ring is the Gaussian integers, with `deg [α] = N(α) = α ᾱ` and
dual `[α]^ = [ᾱ]`.  Its group of torsion points is `(ℚ/ℤ)²` with `ℤ[i]` acting
through the matrix `u + v i ↦ ((u, -v), (v, u))`. -/

-- [dropped: platform already declares QZ]
-- [dropped: platform already declares QZ_divisible]
-- [dropped: platform already declares QZfrac]
theorem QZfrac_apply (n : ℕ) (k : ℤ) :
    QZfrac n k = QuotientAddGroup.mk ((k : ℚ) / n) := by
  simp [QZfrac, zsmul_eq_mul, div_eq_mul_inv]

/-- An element of `ℚ/ℤ` is zero exactly when a representative is an integer. -/
theorem QZ_mk_eq_zero (x : ℚ) :
    (QuotientAddGroup.mk x : QZ) = 0 ↔ ∃ k : ℤ, (k : ℚ) = x := by
  rw [show (0 : QZ) = QuotientAddGroup.mk 0 by rfl]
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simp [AddSubgroup.mem_zmultiples_iff]

/-- The kernel of `k ↦ k/n` is `nℤ`. -/
theorem QZ_ker_QZfrac {n : ℕ} (hn : 0 < n) :
    (QZfrac n).ker = AddSubgroup.zmultiples (n : ℤ) := by
  ext k
  simp only [AddMonoidHom.mem_ker, QZfrac_apply, QZ_mk_eq_zero]
  have hn' : (n : ℚ) ≠ 0 := by norm_cast; linarith
  constructor
  · rintro ⟨m, hm⟩
    exact ⟨m, by rw [eq_div_iff hn'] at hm; norm_cast at hm⟩
  · rintro ⟨m, rfl⟩
    refine ⟨m, ?_⟩
    field_simp
    norm_cast

/-- The image of `k ↦ k/n` is the `n`-torsion of `ℚ/ℤ`. -/
theorem QZ_range_QZfrac {n : ℕ} (hn : 0 < n) :
    (QZfrac n).range = nTorsion QZ n := by
  ext x
  simp only [AddMonoidHom.mem_range, mem_nTorsion]
  have hn' : (n : ℚ) ≠ 0 := by norm_cast; linarith
  constructor
  · rintro ⟨k, rfl⟩
    rw [QZfrac_apply]
    have h1 : (n : ℤ) • (QuotientAddGroup.mk ((k : ℚ) / n) : ℚ ⧸ AddSubgroup.zmultiples 1) =
            QuotientAddGroup.mk ((n : ℚ) * ((k : ℚ) / n)) := by
      simp
    rw [h1]
    have h2 : (n : ℚ) * ((k : ℚ) / n) = k := by field_simp
    rw [h2, QZ_mk_eq_zero]
    exact ⟨k, rfl⟩
  · intro hx
    obtain ⟨q, hq⟩ := Quotient.exists_rep x
    rw [← hq] at hx ⊢
    rw [show (n : ℤ) • (QuotientAddGroup.mk q : QZ) = QuotientAddGroup.mk ((n : ℚ) * q) by
      simp, QZ_mk_eq_zero] at hx
    obtain ⟨k, hk⟩ := hx
    refine ⟨k, ?_⟩
    rw [QZfrac_apply]
    congr 1
    field_simp
    linarith

-- [dropped: platform already declares gaussHom]
-- [dropped: platform already declares gaussHom_apply]
-- [dropped: platform already declares gaussHom_comp]
-- [dropped: platform already declares gaussHom_conj]
-- [dropped: platform already declares gaussHom_surjective]
-- [dropped: platform already declares gaussHom_add]
-- [dropped: platform already declares gaussHom_one]
-- [dropped: platform already declares cmDiamond]
/-- The degrees of the concrete diamond are coprime, so all results above
apply to it; in particular the theory of Kani diamonds is non-vacuous. -/
theorem cmDiamond_coprime : Nat.Coprime cmDiamond.a cmDiamond.b := by decide

/-- The Kani isogeny of the concrete diamond has `N = 7`. -/
theorem cmDiamond_N : cmDiamond.N = 7 := rfl

/-- Instantiation of Kani's lemma at the concrete Gaussian diamond: the kernel
of the associated `(7,7)`-isogeny of abelian surfaces is exactly the graph of
the `7`-torsion of the second curve. -/
theorem cmDiamond_ker (z : (QZ × QZ) × (QZ × QZ)) :
    cmDiamond.kani z = 0 ↔ ∃ Q, (7 : ℤ) • Q = 0 ∧ z = cmDiamond.graphMap Q := by
  simpa [cmDiamond_N] using cmDiamond.mem_ker_kani_iff cmDiamond_coprime z

-- [dropped: platform already declares gaussHom_mul_apply]
-- [dropped: platform already declares gaussHom_add_apply]
-- [dropped: platform already declares gaussHom_zero]
-- [dropped: platform already declares gaussEnd]
/-- An integer divisible by every positive integer is zero. -/
theorem int_eq_zero_of_forall_dvd {w : ℤ} (h : ∀ m : ℕ, 0 < m → ((m : ℤ) ∣ w)) :
    w = 0 := by
  by_contra hw
  have habs : 0 < w.natAbs := Int.natAbs_pos.mpr hw
  have hdvd := h (w.natAbs + 1) (by linarith)
  obtain ⟨k, hk⟩ := hdvd
  have hk_ne : k ≠ 0 := by
    intro hk0
    rw [hk0, mul_zero] at hk
    exact hw hk
  have hkeq : w.natAbs = (w.natAbs + 1) * k.natAbs := by
    have := congr_arg Int.natAbs hk
    simp [Int.natAbs_mul] at this
    show w.natAbs = (w.natAbs + 1) * k.natAbs
    have heq : |w| + 1 = ((w.natAbs + 1 : ℕ) : ℤ) := by
      rw [Int.abs_eq_natAbs]
      norm_cast
    rw [heq, Int.natAbs_natCast] at this
    exact this
  linarith [Nat.le_mul_of_pos_right (w.natAbs + 1) (Int.natAbs_pos.mpr hk_ne) ]

/-- An integer acting trivially on every point `1/m` of `ℚ/ℤ` is zero. -/
theorem int_eq_zero_of_smul_QZfrac {w : ℤ}
    (h : ∀ m : ℕ, 0 < m → w • QZfrac m 1 = 0) : w = 0 := by
  refine int_eq_zero_of_forall_dvd fun m hm => ?_
  have hw : QZfrac m w = 0 := by
    have h1 : QZfrac m w = w • QZfrac m 1 := by
      rw [← map_zsmul (QZfrac m) w (1 : ℤ), smul_eq_mul, mul_one]
    rw [h1, h m hm]
  have hmem : w ∈ (QZfrac m).ker := hw
  rw [QZ_ker_QZfrac hm, AddSubgroup.mem_zmultiples_iff] at hmem
  obtain ⟨c, hc⟩ := hmem
  exact ⟨c, by rw [← hc, smul_eq_mul, mul_comm]⟩

/-- If multiplication by `u + v i` kills all torsion points, then `u = v = 0`. -/
theorem gaussHom_eq_zero_iff {u v : ℤ} (h : ∀ p, gaussHom u v p = 0) :
    u = 0 ∧ v = 0 := by
  constructor
  · refine int_eq_zero_of_smul_QZfrac fun m hm => ?_
    have hp := h (QZfrac m 1, 0)
    have := congrArg Prod.fst hp
    simpa using this
  · refine int_eq_zero_of_smul_QZfrac fun m hm => ?_
    have hp := h (QZfrac m 1, 0)
    have := congrArg Prod.snd hp
    simpa using this

/-- The complex multiplication action is faithful. -/
theorem gaussEnd_injective : Function.Injective gaussEnd := by
  intro z w hzw
  have key : (z - w).re = 0 ∧ (z - w).im = 0 := by
    apply gaussHom_eq_zero_iff
    intro p
    have := AddMonoidHom.ext_iff.mp hzw p
    simp [gaussEnd, gaussHom] at this ⊢
    have h1 := this.1
    have h2 := this.2
    simp only [sub_zsmul]
    refine ⟨?_, ?_⟩
    · trans (z.re • p.1 - z.im • p.2) - (w.re • p.1 - w.im • p.2)
      · abel
      · rw [h1]; abel
    · trans (z.im • p.1 + z.re • p.2) - (w.im • p.1 + w.re • p.2)
      · abel
      · rw [h2]; abel
  ext <;> simp_all [sub_eq_zero]

/-- The `n`-torsion of `ℚ/ℤ` is cyclic of order `n`. -/
theorem card_nTorsion_QZ {n : ℕ} (hn : 0 < n) : Nat.card (nTorsion QZ n) = n := by
  rw [← QZ_range_QZfrac hn,
    ← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (QZfrac n)).toEquiv,
    QZ_ker_QZfrac hn,
    Nat.card_congr (Int.quotientZMultiplesNatEquivZMod n).toEquiv, Nat.card_zmod]

/-- The concrete Kani isogeny has kernel of order `N² = 49`, as predicted by
Kani's lemma. -/
theorem cmDiamond_card_ker : Nat.card cmDiamond.kani.ker = 49 := by
  have h : Nat.card (nTorsion (QZ × QZ) cmDiamond.N) = cmDiamond.N ^ 2 := by
    rw [cmDiamond_N, card_nTorsion_prod, card_nTorsion_QZ (by norm_num)]
    ring
  have := cmDiamond.card_ker_kani cmDiamond_coprime h
  rwa [cmDiamond_N] at this

end Diamond

end Cryptography.SIDH
section
open Cryptography.SIDH
open Diamond
variable {E₁ E₂ E₃ E₄ : Type*} [AddCommGroup E₁] [AddCommGroup E₂]

theorem solution  :
    Function.Injective gaussEnd :=
  Cryptography.SIDH.Diamond.gaussEnd_injective

end
