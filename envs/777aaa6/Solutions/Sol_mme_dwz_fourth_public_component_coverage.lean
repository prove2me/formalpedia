-- Prove2me | solution 1 for mme_dwz_fourth_public_component_coverage
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T05:05:44.421598+00:00
-- url     : https://prove2.me/submissions/9a5999cc-0c65-4c2d-b030-d32220c5542c

import Definitions.Def_mme_dwz_fourth_public_component_coverage_data
import Theorems.Thm_mme_dwz_fourth_tensor_ledger_metadata

open MME MME.DWZFourthTensorLedger
open scoped Classical

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthTensorLedger

/-- Exact machine-checked coverage census.  The seven numbers sum to 180. -/
private theorem publicCoverageCounts :
    publicCoverageCount .atomicExactMM = 6 ∧
    publicCoverageCount .squareElementaryBoundary = 9 ∧
    publicCoverageCount .square022PrescribedZ = 19 ∧
    publicCoverageCount .square022CyclicTransport = 38 ∧
    publicCoverageCount .square112ProfileTransport = 63 ∧
    publicCoverageCount .fourthElementaryBoundary = 24 ∧
    publicCoverageCount .fourthPositivePrescribedZOpen = 21 := by
  decide +kernel

/-- There are exactly 21 positive fourth rows.  This explicit list is useful
for checking that a recursive tensor certificate covers precisely the intended
frontier rather than an unnamed collection of coarse blocks. -/
private theorem positiveSixRegionObjectIds_eq :
    positiveSixRegionObjectIds =
      [149, 150, 151, 152, 153, 154,
       157, 158, 159, 160, 161,
       164, 165, 166, 167,
       170, 171, 172,
       175, 176, 179] := by
  decide +kernel

private theorem positiveSixRegionAddressCodes_eq :
    positiveSixRegionAddressCodes =
      [116, 125, 134, 143, 152, 161,
       215, 224, 233, 242, 251,
       314, 323, 332, 341,
       413, 422, 431,
       512, 521, 611] := by
  decide +kernel

private theorem nonPositiveProperComponentCount :
    (componentMetadata.toList.filter fun metadata ↦
      publicCoverageTier metadata ≠
        PublicCoverageTier.fourthPositivePrescribedZOpen).length = 159 := by
  decide +kernel

private theorem directPublicPrescribedZEndpointCount :
    (componentMetadata.toList.filter
      hasDirectPublicPrescribedZEndpoint).length = 19 := by
  decide +kernel

private theorem requiresPrescribedZBridgeCount :
    (componentMetadata.toList.filter requiresPrescribedZBridge).length = 161 := by
  decide +kernel

/-- Six atomic, 24 square-boundary, and ten fourth-boundary records have a
one-hot prescribed profile.  No 112-family or positive fourth record does. -/
private theorem oneHotLedgerZProfileCounts :
    (componentMetadata.toList.filter hasOneHotLedgerZProfile).length = 40 ∧
    (componentMetadata.toList.filter fun metadata =>
      hasOneHotLedgerZProfile metadata &&
        publicCoverageTier metadata = .atomicExactMM).length = 6 ∧
    (componentMetadata.toList.filter fun metadata =>
      hasOneHotLedgerZProfile metadata &&
        publicCoverageTier metadata = .squareElementaryBoundary).length = 5 ∧
    (componentMetadata.toList.filter fun metadata =>
      hasOneHotLedgerZProfile metadata &&
        publicCoverageTier metadata = .square022CyclicTransport).length = 19 ∧
    (componentMetadata.toList.filter fun metadata =>
      hasOneHotLedgerZProfile metadata &&
        publicCoverageTier metadata = .fourthElementaryBoundary).length = 10 := by
  decide +kernel

private theorem requiresNontrivialPrescribedZBridgeCount :
    (componentMetadata.toList.filter
      requiresNontrivialPrescribedZBridge).length = 121 := by
  decide +kernel

/-- The direct prescribed-Z theorem, its two cyclic transports, and the three
112-family orientations account for 120 of the 129 reachable square rows. -/
private theorem squareCentralAndCoupledCount :
    (componentMetadata.toList.filter fun metadata =>
      publicCoverageTier metadata = .square022PrescribedZ ∨
      publicCoverageTier metadata = .square022CyclicTransport ∨
      publicCoverageTier metadata = .square112ProfileTransport).length = 120 := by
  decide +kernel

private theorem publicCyclicStarExactLedgerMatchCount :
    (componentMetadata.toList.filter fun metadata =>
      publicCoverageTier metadata = .square112ProfileTransport &&
        matchesPublicCyclicStarZShape metadata).length = 0 := by
  decide +kernel

private theorem componentSpecAt_mem_componentMetadata (i : Fin 180) :
    componentSpecAt i ∈ componentMetadata.toList := by
  simp [componentSpecAt]

/-- The canonicalized counts have the exact declared denominator on every
one of the 63 coupled rows. -/
private theorem canonicalCyclicProfileNormalization :
    ∀ metadata ∈ componentMetadata.toList,
      publicCoverageTier metadata = PublicCoverageTier.square112ProfileTransport →
        List.sum (canonicalCyclicZCounts metadata) =
          canonicalCyclicZDenominator metadata := by
  decide +kernel

/-- All twenty-one literal 112 triples satisfy the public balance range after
the single exact `p = 1/10` retuning, hence all three orientations of all
triples (63 ledger rows) are exact f432/5fb profile instances. -/
private theorem canonicalCyclicEligibleCounts :
    (componentMetadata.toList.filter fun metadata =>
      metadata.address = .square 1 1 2 ∧
        hasCanonicalCyclicBalance metadata).length = 21 ∧
    (componentMetadata.toList.filter fun metadata =>
      publicCoverageTier metadata = .square112ProfileTransport &&
        hasCanonicalCyclicBalance metadata).length = 63 := by
  decide +kernel

/-- No canonicalized cyclic row remains outside the public balance range. -/
private theorem canonicalCyclicIneligibleObjectIds :
    (componentMetadata.toList.filter (fun metadata =>
      publicCoverageTier metadata = .square112ProfileTransport &&
        !hasCanonicalCyclicBalance metadata)).map
          ComponentMetadata.objectId = [] := by
  decide +kernel

/-- The cyclic orbit containing the single retuned literal anchor is exactly
objects 76/77/78. -/
private theorem retunedExceptionalCyclicObjectIds :
    (componentMetadata.toList.filter (fun metadata =>
      publicCoverageTier metadata = .square112ProfileTransport &&
        isRetunedExceptionalCyclicTriple metadata)).map
          ComponentMetadata.objectId = [76, 77, 78] := by
  decide +kernel

/-- Machine-checked end-to-end match count for the canonicalized profiles:
all 63 coupled ledger rows have the exact literal/cyclic Z-shape and satisfy
the strict balance premise of `f432e635`. -/
private theorem canonicalCyclicStarExactMatchCount :
    (componentMetadata.toList.filter fun metadata =>
      publicCoverageTier metadata = .square112ProfileTransport &&
        hasCanonicalCyclicBalance metadata &&
        match metadata.address, canonicalCyclicZCounts metadata with
        | .square i j k, [a, b, c] =>
            if i.val = 1 ∧ j.val = 1 ∧ k.val = 2 then
              a == canonicalCyclicL metadata &&
                b == 2 * canonicalCyclicG metadata &&
                c == canonicalCyclicL metadata
            else if (i.val = 1 ∧ j.val = 2 ∧ k.val = 1) ∨
                (i.val = 2 ∧ j.val = 1 ∧ k.val = 1) then
              a == canonicalCyclicL metadata + canonicalCyclicG metadata &&
                b == canonicalCyclicL metadata + canonicalCyclicG metadata &&
                c == 0
            else false
        | _, _ => false).length = 63 := by
  decide +kernel

private theorem canonicalCyclicOrientationMatches_iff
    (metadata : ComponentMetadata) :
    canonicalCyclicOrientationMatches metadata = true ↔
      CanonicalCyclicProfileShape metadata := by
  cases haddress : metadata.address <;>
    simp [canonicalCyclicOrientationMatches, CanonicalCyclicProfileShape,
      haddress]

/-- A row-indexed certificate exposing exactly the numerical premises needed
to specialize the public cyclic source theorem and the exact prescribed-Z
pushforward.  Unlike the census above, this theorem is directly consumable by
the 181-node integration after a coupled row is selected. -/
private theorem canonicalCyclicLedgerPremises :
    ∀ metadata ∈ componentMetadata.toList,
      publicCoverageTier metadata =
          PublicCoverageTier.square112ProfileTransport →
        let l := canonicalCyclicL metadata
        let g := canonicalCyclicG metadata
        341 * l < 100 * g ∧
          canonicalCyclicZDenominator metadata = 2 * (l + g) ∧
          canonicalCyclicOrientationMatches metadata = true := by
  decide +kernel

private theorem canonicalCyclicLedgerPremisesProp
    (metadata : ComponentMetadata)
    (hmem : metadata ∈ componentMetadata.toList)
    (htier : publicCoverageTier metadata =
      PublicCoverageTier.square112ProfileTransport) :
    let l := canonicalCyclicL metadata
    let g := canonicalCyclicG metadata
    341 * l < 100 * g ∧
      canonicalCyclicZDenominator metadata = 2 * (l + g) ∧
      CanonicalCyclicProfileShape metadata := by
  rcases canonicalCyclicLedgerPremises metadata hmem htier with
    ⟨hbalance, hden, hshape⟩
  exact ⟨hbalance, hden,
    (canonicalCyclicOrientationMatches_iff metadata).mp hshape⟩

end MME.DWZFourthTensorLedger

theorem solution :
    ((componentMetadata.toList.filter hasOneHotLedgerZProfile).length = 40 ∧
      (componentMetadata.toList.filter fun metadata =>
        hasOneHotLedgerZProfile metadata &&
          publicCoverageTier metadata = .atomicExactMM).length = 6 ∧
      (componentMetadata.toList.filter fun metadata =>
        hasOneHotLedgerZProfile metadata &&
          publicCoverageTier metadata = .squareElementaryBoundary).length = 5 ∧
      (componentMetadata.toList.filter fun metadata =>
        hasOneHotLedgerZProfile metadata &&
          publicCoverageTier metadata = .square022CyclicTransport).length = 19 ∧
      (componentMetadata.toList.filter fun metadata =>
        hasOneHotLedgerZProfile metadata &&
          publicCoverageTier metadata = .fourthElementaryBoundary).length = 10) ∧
    (∀ (i : Fin 180),
      componentSpecAt i ∈ componentMetadata.toList) ∧
    (∀ (metadata : ComponentMetadata) (hmem : metadata ∈ componentMetadata.toList) (htier : publicCoverageTier metadata = PublicCoverageTier.square112ProfileTransport),
      let l := canonicalCyclicL metadata
      let g := canonicalCyclicG metadata
      341 * l < 100 * g ∧
        canonicalCyclicZDenominator metadata = 2 * (l + g) ∧
        CanonicalCyclicProfileShape metadata) :=
  ⟨oneHotLedgerZProfileCounts, componentSpecAt_mem_componentMetadata, canonicalCyclicLedgerPremisesProp⟩
