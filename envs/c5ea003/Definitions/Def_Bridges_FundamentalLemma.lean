-- Prove2me | Definitions.Def_Bridges_FundamentalLemma
-- name    : Bridges_FundamentalLemma
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:21:39.578057+00:00
-- url     : https://prove2.me/theorems/d95f9100-6d05-4ab9-840d-8b05435218f6
-- title:
--   Aether Catalog definitions — Bridges_FundamentalLemma
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.FundamentalLemma`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/FundamentalLemma.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Tropical.Langlands.FundamentalLemma

Auto-generated from theorem catalog database.
Domain: Tropical/Langlands
Declarations: 26
-/

noncomputable section

/-- A tropical conjugacy class is parametrized by sorted eigenvalues (Newton polygon slopes) -/
structure TropicalConjClass (n : ℕ) where
  eigenvalues : Fin n → ℝ
  sorted : ∀ i j : Fin n, i ≤ j → eigenvalues i ≤ eigenvalues j

/-- The tropical orbital integral: sum of eigenvalues (= trace in tropical sense) -/
def tropicalOrbitalIntegral (n : ℕ) (γ : TropicalConjClass n) : ℝ :=
  ∑ i : Fin n, γ.eigenvalues i

/-- The tropical stable orbital integral: sum weighted by stability factor -/
def tropicalStableOrbitalIntegral (n : ℕ) (γ : TropicalConjClass n)
    (κ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, κ i * γ.eigenvalues i

/-- The tropical transfer factor between G and an endoscopic group H -/
def tropicalTransferFactor (n : ℕ) (γ_G γ_H : TropicalConjClass n) : ℝ :=
  ∑ i : Fin n, (γ_G.eigenvalues i - γ_H.eigenvalues i)



/-- GL₁ conjugacy class is just a single real number -/
def GL1ConjClass (a : ℝ) : TropicalConjClass 1 where
  eigenvalues := fun _ => a
  sorted := fun _ _ _ => le_refl _



/-- GL₂ conjugacy class from eigenvalues a ≤ b -/
def GL2ConjClass (a b : ℝ) (h : a ≤ b) : TropicalConjClass 2 where
  eigenvalues := ![a, b]
  sorted := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [Matrix.cons_val_zero, Matrix.cons_val_one]







/-- Tropical base change: scaling eigenvalues by a degree d -/
def tropicalBaseChange (n : ℕ) (γ : TropicalConjClass n) (d : ℝ) (hd : d > 0) :
    TropicalConjClass n where
  eigenvalues := fun i => d * γ.eigenvalues i
  sorted := fun i j h => by
    apply mul_le_mul_of_nonneg_left (γ.sorted i j h) (le_of_lt hd)



/-- The κ-orbital integral with character κ -/
def kappaOrbitalIntegral (n : ℕ) (γ : TropicalConjClass n) (κ : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, κ i * γ.eigenvalues i




/-- Tropical Hitchin base: the coefficients of the characteristic polynomial
are the elementary symmetric functions of the eigenvalues -/
def tropicalHitchinBase (n : ℕ) (γ : TropicalConjClass n) : Fin n → ℝ :=
  γ.eigenvalues  -- In the tropical setting, eigenvalues = Hitchin base coordinates



end


