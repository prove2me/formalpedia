-- Prove2me | Definitions.Def_Bridges_SauerShelah
-- name    : Bridges_SauerShelah
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:39:11.205016+00:00
-- url     : https://prove2.me/theorems/eecc79c9-6964-42ef-ba02-06da8295218c
-- title:
--   Aether Catalog definitions — Bridges_SauerShelah
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.SauerShelah`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/SauerShelah.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Bridges.SauerShelah

Auto-generated from theorem catalog database.
Domain: Bridges
Declarations: 12
-/

noncomputable section

/-- The restriction of a family to a subset S -/
def restrictFamily {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (S : Finset α) : Finset (Finset α) :=
  F.image (· ∩ S)




/-- A family F shatters S if every subset of S appears as a restriction -/
def Shatters' {α : Type*} [DecidableEq α]
    (F : Finset (Finset α)) (S : Finset α) : Prop :=
  S.powerset ⊆ restrictFamily F S



/-- Sum of binomial coefficients up to d -/
def binomialSum (n d : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (d + 1), n.choose i





end


