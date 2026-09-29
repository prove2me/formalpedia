-- Prove2me | Definitions.Def_Bridges_PadicLanglandsGL2
-- name    : Bridges_PadicLanglandsGL2
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:07.971756+00:00
-- url     : https://prove2.me/theorems/9913833a-845d-451c-b19a-c6c2c16cd6ba
-- title:
--   Aether Catalog definitions — Bridges_PadicLanglandsGL2
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PadicLanglandsGL2`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PadicLanglandsGL2.lean by skeleton subtraction
import Mathlib
/-
# p-adic Langlands for GL₂(ℚ_p): a foundational chain

This file develops a self-contained chain of results around the two sides of the
**p-adic Langlands correspondence for `GL₂(ℚ_p)`**:

* the **automorphic / `GL₂` side**: the group `GL₂(K)` over a field `K`
  (specialised to `K = ℚ_p = Padic p`), its scalar centre, the determinant
  character, and the abelian (`GL₁`) part of the correspondence;
* the **Galois side**: `2`-dimensional representations `ρ : G →* GL₂(ℚ_p)` of an
  abstract group `G` (a stand-in for `Gal(ℚ̄_p/ℚ_p)`), their determinant
  characters, and the compatibility of determinants with character twists.

The chain, each step feeding the next:

1. `matrix_two_cayley_hamilton` — the explicit Cayley–Hamilton identity for `2×2`
   matrices, `M * M = tr M • M - det M • 1` (the characteristic polynomial of a
   `2`-dimensional representation).
2. `matrix_two_adjugate` — the adjugate identity `M * (tr M • 1 - M) = det M • 1`,
   deduced from (1); it exhibits the inverse of a `GL₂` element.
3. `diagGL`, `diagGL_det`, `det_surjective` — the determinant `GL₂(K) →* Kˣ` is
   surjective.
4. `detCharCorrespondence` — the resulting bijection between characters of `Kˣ`
   and characters of `GL₂(K)` that are trivial on `SL₂(K) = ker det`.  This is the
   abelian (`GL₁`) shadow of the local Langlands correspondence: twisting
   characters of `GL₂` are exactly characters of `Kˣ`.
5. `scalarGL`, `scalarGL_det`, `scalarGL_comm` — the central scalar embedding
   `Kˣ →* GL₂(K)` and its determinant (the squaring map).
6. `twistRep`, `twistRep_det` — twisting a `2`-dimensional representation by a
   character multiplies the determinant character by the square of the twisting
   character, `det(χ ⊗ ρ) = χ² · det ρ`, the standard Galois-side compatibility.
7. p-adic specialisations (`Padic p = ℚ_p`) of the above.

Everything is proved from `Mathlib` with no axioms beyond the standard ones.
-/

open Matrix Polynomial

namespace PadicLanglandsGL2

/-! ## The characteristic polynomial of a 2-dimensional representation -/

variable {K : Type*} [Field K]



/-! ## The determinant character is surjective -/

/-- The diagonal element `diag(u, 1)` of `GL₂(K)` attached to a unit `u : Kˣ`. -/
noncomputable def diagGL (u : Kˣ) : GL (Fin 2) K where
  val := Matrix.diagonal ![(u : K), 1]
  inv := Matrix.diagonal ![((u⁻¹ : Kˣ) : K), 1]
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i; fin_cases i <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1; ext i; fin_cases i <;> simp

/-- The determinant of `diag(u, 1)` is `u`. -/
theorem diagGL_det (u : Kˣ) : Matrix.GeneralLinearGroup.det (diagGL u) = u := by
  ext; rw [GeneralLinearGroup.val_det_apply]; simp [diagGL]

/-- **The determinant is a surjective homomorphism `GL₂(K) →* Kˣ`.**  This is the
`GL₂ ↠ GL₁` reciprocity underlying the abelian part of the correspondence. -/
theorem det_surjective :
    Function.Surjective (Matrix.GeneralLinearGroup.det : GL (Fin 2) K →* Kˣ) :=
  fun u => ⟨diagGL u, diagGL_det u⟩


/-- **The abelian (`GL₁`) part of the local Langlands correspondence.**

For any target group `A`, the determinant induces a bijection between
homomorphisms `Kˣ →* A` and homomorphisms `GL₂(K) →* A` that are trivial on
`SL₂(K) = ker det`.  Concretely: the "twisting characters" of `GL₂(K)` are
exactly the characters of `Kˣ`, pulled back along the determinant. -/
noncomputable def detCharCorrespondence {A : Type*} [Group A] :
    { f : GL (Fin 2) K →* A //
        (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K)).ker ≤ f.ker } ≃ (Kˣ →* A) :=
  MonoidHom.liftOfSurjective _ det_surjective



/-! ## The scalar (central) embedding `Kˣ →* GL₂(K)` -/

/-- The central scalar embedding `Kˣ →* GL₂(K)`, `u ↦ u • 1`. -/
noncomputable def scalarGL : Kˣ →* GL (Fin 2) K :=
  Units.map (Matrix.scalar (Fin 2)).toMonoidHom


/-- Scalar matrices are central in `GL₂(K)`. -/
theorem scalarGL_comm (a : Kˣ) (g : GL (Fin 2) K) :
    scalarGL a * g = g * scalarGL a := by
  ext i j
  simp only [scalarGL, Units.map]
  show (Matrix.scalar (Fin 2) (a : K) * (g : Matrix (Fin 2) (Fin 2) K)) i j
     = ((g : Matrix (Fin 2) (Fin 2) K) * Matrix.scalar (Fin 2) (a : K)) i j
  rw [Matrix.scalar_commute _ (fun r => Commute.all _ _)]

/-! ## The Galois side: 2-dimensional representations and twists -/

variable {G : Type*} [Group G]

/-- **Twisting a `2`-dimensional representation by a character.**  Given a
representation `ρ : G →* GL₂(K)` and a character `χ : G →* Kˣ`, the twist
`χ ⊗ ρ` sends `g` to `χ(g) • ρ(g)`.  Because scalars are central this is again a
homomorphism. -/
noncomputable def twistRep (χ : G →* Kˣ) (ρ : G →* GL (Fin 2) K) : G →* GL (Fin 2) K where
  toFun g := scalarGL (χ g) * ρ g
  map_one' := by simp
  map_mul' g h := by
    simp only [map_mul, mul_assoc]
    rw [← mul_assoc (scalarGL (χ h)), scalarGL_comm (χ h) (ρ g),
        mul_assoc (ρ g) (scalarGL (χ h)) (ρ h)]

/-- The determinant character of a `2`-dimensional representation `ρ`, i.e.
`det ∘ ρ : G →* Kˣ`.  Under local class field theory this is the central
character of the corresponding `GL₂` representation. -/
noncomputable def detRep (ρ : G →* GL (Fin 2) K) : G →* Kˣ :=
  (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K)).comp ρ


/-! ## Specialisation to `K = ℚ_p = Padic p` -/

section Padic

variable (p : ℕ) [hp : Fact p.Prime]





end Padic

end PadicLanglandsGL2


