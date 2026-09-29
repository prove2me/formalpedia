-- Prove2me | Definitions.Def_Applications_EML_Transseries
-- name    : Applications_EML_Transseries
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:44:47.006058+00:00
-- url     : https://prove2.me/theorems/1bb2ed53-de96-4ede-9a71-f20692b52611
-- title:
--   Aether Catalog definitions — Applications_EML_Transseries
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.EML.Transseries`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/EML/Transseries.lean by skeleton subtraction
import Mathlib

/-!
# Hahn-series foundations for exponential–logarithmic transseries

A transseries is represented here by a Hahn series.  Its ordered exponent records
three successive growth levels (exponential, polynomial, and logarithmic).  The
central result is the asymptotic comparison principle: equality of every formal
order is equivalent to equality of transseries.  For unequal series, the order of
their difference is proved to be the first order at which their coefficients can
differ.
-/

noncomputable section

open HahnSeries

namespace EMLTransseries

/-- Three lexicographically ordered growth levels.  The coordinates can encode,
respectively, exponential, polynomial, and logarithmic scales. -/
abbrev GrowthRank := ℤ ×ₗ (ℤ ×ₗ ℤ)

/-- Formal EML transseries with real coefficients and three growth levels. -/
abbrev Transseries := HahnSeries GrowthRank ℝ

/-- Two transseries agree strictly below `cut` when all coefficients at smaller
orders coincide. -/
def AgreeBelow (f g : Transseries) (cut : GrowthRank) : Prop :=
  ∀ rank, rank < cut → f.coeff rank = g.coeff rank

/-- Two transseries agree to all orders when every coefficient agrees. -/
def AgreeToAllOrders (f g : Transseries) : Prop :=
  ∀ rank, f.coeff rank = g.coeff rank

/-- A single transmonomial at a specified growth rank. -/
def monomial (rank : GrowthRank) (c : ℝ) : Transseries :=
  HahnSeries.single rank c












end EMLTransseries


