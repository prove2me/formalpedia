-- Prove2me | Definitions.Def_mme_regional_certified_log_copy_bound
-- name    : mme_regional_certified_log_copy_bound
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-21T20:02:19.906244+00:00
-- url     : https://prove2.me/theorems/26667c13-7a7f-4c23-8dba-a53f929d0f31
-- title:
--   Regional copy rate with every finite loss explicit
-- statement:
--   Defines the logarithmic copy guarantee of an actual integer regional extraction step. Starting from the summed entropy rate, subtracts the entropy-continuity loss, the AP-free-set square-root loss, the polynomial and constant factors, and the hole-repair exponent times log 8. The factor 64 pays explicitly for integer rounding. This definition by itself asserts no extraction or stronger exponent.
-- source:
--   Derived from the proved regional entropy copy bound; More Asymmetry, arXiv:2404.16349v2, recursive hashing and hole repair.

import Definitions.Def_mme_regional_entropy_copy_bound
open BigOperators
set_option autoImplicit false
namespace MME.RegionRealization

/-- Guaranteed logarithmic copy rate, paying for entropy continuity, the
AP-free-set bound, polynomial losses, integer rounding, and hole repair. -/
noncomputable def IntegerStep.certifiedLogCopies {ell M : ℕ}
    {P : ProfiledCW.Predicate M} (D : IntegerStep ell M P) : ℝ :=
  let E := RegionRate.regionalRate D.total D.n D.m D.mu
  let loss := ((∑ r, D.n r : ℕ) : ℝ) *
    RegionRate.entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) D.epsilon
  let theta := RegionRate.scaleExponent D.total D.n D.m D.mu D.epsilon
  let factor := RegionRate.scaleFactor (half := D.half) (parent := D.parent)
    D.n D.repairScale ell
  E - loss - 4 * Real.sqrt (Real.log factor + theta) -
    Real.log (64 * RegionRate.polynomialFactor D.n
      (Fintype.card (RecursiveYZ.Cell D.half D.R D.parent)) * factor) -
    D.repairExponent * Real.log 8

end MME.RegionRealization


