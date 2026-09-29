-- Prove2me | solution 1 for flt5_zz5_norm_galois_prod
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-05-13T16:35:40.419224+00:00
-- url     : https://prove2.me/submissions/a88c01c0-f977-46c9-89be-77d0b887853e

import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.Int.Basic

-- v5 fixes (v4 + replace native_decide -> decide):
-- (1) isGalois {5} not 5 (Set ℕ vs ℕ bug)
-- (2) autEquivPow CK5gp4 h_irred (L explicit, no hμ)
-- (3) autToPow_injective ℚ hζ (explicit K to avoid Field K✝)
-- (4) use "have hprod := Fintype.prod_bijective ... ; rw [hprod]" to give
--     Lean goal-type context before typeclass synthesis (fixes Field K✝ in rw)

noncomputable section

abbrev CK5gp4 := CyclotomicField 5 ℚ

instance : IsCyclotomicExtension {5} ℚ CK5gp4 :=
  CyclotomicField.isCyclotomicExtension 5 ℚ

instance : NumberField CK5gp4 :=
  IsCyclotomicExtension.numberField {5} ℚ CK5gp4

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

instance : IsGalois ℚ CK5gp4 :=
  IsCyclotomicExtension.isGalois {5} ℚ CK5gp4

theorem solution (a b : ℤ) (ζ : CK5gp4) (hζ : IsPrimitiveRoot ζ 5) :
    algebraMap ℚ CK5gp4 (Algebra.norm ℚ ((a : CK5gp4) + ζ * b)) =
    ((a : CK5gp4) + ζ * b) * (a + ζ ^ 2 * b) * (a + ζ ^ 3 * b) * (a + ζ ^ 4 * b) := by
  have h_irred : Irreducible (Polynomial.cyclotomic 5 ℚ) :=
    Polynomial.cyclotomic.irreducible_rat (by norm_num)
  -- autEquivPow : Gal(CK5gp4/ℚ) ≃* (ZMod 5)ˣ (L explicit, K implicit from h_irred)
  let e_iso := IsCyclotomicExtension.autEquivPow CK5gp4 h_irred
  -- Step 1: norm = product over Galois group
  rw [Algebra.norm_eq_prod_automorphisms]
  -- Step 2: σ fixes integers → σ(a + ζ*b) = a + σ(ζ)*b
  simp_rw [show ∀ σ : CK5gp4 ≃ₐ[ℚ] CK5gp4,
      σ ((a : CK5gp4) + ζ * b) = (a : CK5gp4) + σ ζ * b from
    fun σ => by simp [map_add, map_mul, map_intCast]]
  -- Step 3: bijectivity of autToPow (K explicit to prevent Field K✝)
  have hinj : Function.Injective (hζ.autToPow ℚ) :=
    IsPrimitiveRoot.autToPow_injective ℚ hζ
  have hbij : Function.Bijective (hζ.autToPow ℚ) :=
    ⟨hinj, Finite.injective_iff_surjective_of_equiv e_iso.toEquiv |>.mp hinj⟩
  -- Step 4: reindex product (use have+rw so goal type is known before typeclass synthesis)
  have hprod : ∏ σ : (CK5gp4 ≃ₐ[ℚ] CK5gp4), ((a : CK5gp4) + σ ζ * b) =
               ∏ k : (ZMod 5)ˣ, ((a : CK5gp4) + ζ ^ (k : ZMod 5).val * b) :=
    Fintype.prod_bijective (hζ.autToPow ℚ) hbij _ _ (fun σ => by
      show (a : CK5gp4) + σ ζ * b =
        (a : CK5gp4) + ζ ^ ((hζ.autToPow ℚ σ : ZMod 5).val) * b
      rw [← hζ.autToPow_spec ℚ σ])
  rw [hprod]
  -- Step 5: enumerate (ZMod 5)ˣ = {u1, u2, u3, u4}
  have huniv : (Finset.univ : Finset (ZMod 5)ˣ) =
      {ZMod.unitOfCoprime 1 (by decide), ZMod.unitOfCoprime 2 (by decide),
       ZMod.unitOfCoprime 3 (by decide), ZMod.unitOfCoprime 4 (by decide)} := by
    decide
  have hv1 : (ZMod.unitOfCoprime 1 (by decide : Nat.Coprime 1 5) : ZMod 5).val = 1 :=
    by decide
  have hv2 : (ZMod.unitOfCoprime 2 (by decide : Nat.Coprime 2 5) : ZMod 5).val = 2 :=
    by decide
  have hv3 : (ZMod.unitOfCoprime 3 (by decide : Nat.Coprime 3 5) : ZMod 5).val = 3 :=
    by decide
  have hv4 : (ZMod.unitOfCoprime 4 (by decide : Nat.Coprime 4 5) : ZMod 5).val = 4 :=
    by decide
  rw [huniv,
      Finset.prod_insert (by decide),
      Finset.prod_insert (by decide),
      Finset.prod_insert (by decide),
      Finset.prod_singleton,
      hv1, hv2, hv3, hv4, pow_one]
  ring

end
