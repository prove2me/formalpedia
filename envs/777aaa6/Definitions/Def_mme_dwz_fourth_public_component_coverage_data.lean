-- Prove2me | Definitions.Def_mme_dwz_fourth_public_component_coverage_data
-- name    : mme_dwz_fourth_public_component_coverage_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-21T05:05:08.106427+00:00
-- url     : https://prove2.me/theorems/bbc7a22e-c39b-4d54-845f-599b3df7283c
-- title:
--   Public-theorem coverage of the 180 fourth-power ledger rows
-- statement:
--   Definitions used by the statement of mme_dwz_fourth_public_component_coverage, from the exact fourth-power scalar assembly.
-- source:
--   Formalization of the exact rational scalar certificate and the tensor assembly of the Duan-Wu-Zhou fourth-power construction. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 .

import Definitions.Def_mme_dwz_fourth_tensor_ledger_metadata_data
import Theorems.Thm_mme_dwz_fourth_tensor_ledger_metadata

open scoped Classical

set_option autoImplicit false

set_option maxRecDepth 4000000
set_option maxHeartbeats 0

namespace MME.DWZFourthTensorLedger

/--
The finest honest partition of the 180 tensor-ledger rows by the public
component result that can currently be attached to them.

The constructors deliberately distinguish an actual prescribed-Z endpoint
from an ordinary value/normalization result.  In particular, the public 022
endpoint is oriented: its statement prescribes the third (`Z`) mode of the
literal canonical 022 block.  The 202 and 220 rows therefore remain a
separate transport obligation even though their ordinary symmetric values
follow by cyclic permutation.
-/
inductive PublicCoverageTier where
  /-- One of the six support blocks of `CWObj`; each has a public exact-MM
  restriction theorem `mme_CW_block_is_MM_at_*`. -/
  | atomicExactMM
  /-- The nine noncentral boundary blocks of `CWObj ⊗ CWObj`.  They are
  products of the six atomic blocks; no prescribed-Z theorem is needed. -/
  | squareElementaryBoundary
  /-- Literal canonical 022 rows, covered by
  `mme_dwz_canonical022_prescribed_z_six_restriction_value`. -/
  | square022PrescribedZ
  /-- Literal 202 and 220 rows.  They are in the cyclic orbit of 022, but the
  existing public prescribed-Z endpoint has not transported its distinguished
  Z-basis/profile to these orientations. -/
  | square022CyclicTransport
  /-- The 112/121/211 rows.  Their canonical restrictions to `coupledObj` and
  the generic-q symmetric scalar value are public; their individual exact
  prescribed-Z profile endpoint is the remaining distinction. -/
  | square112ProfileTransport
  /-- The 24 fourth-power addresses having a zero coordinate.  The five orbit
  representatives 008, 017, 026, 035, 044 have public exact-MM restrictions;
  mode permutations cover the other representatives at ordinary value level. -/
  | fourthElementaryBoundary
  /-- The 21 positive fourth-power addresses.  Public entropy/scalar
  certificates exist, but no per-row prescribed-Z restriction endpoint does. -/
  | fourthPositivePrescribedZOpen
deriving DecidableEq, Repr

def publicCoverageTier (metadata : ComponentMetadata) : PublicCoverageTier :=
  match metadata.address with
  | .base .. => .atomicExactMM
  | .square i j k =>
      if i.val = 0 ∧ j.val = 2 ∧ k.val = 2 then
        .square022PrescribedZ
      else if (i.val = 2 ∧ j.val = 0 ∧ k.val = 2) ∨
          (i.val = 2 ∧ j.val = 2 ∧ k.val = 0) then
        .square022CyclicTransport
      else if metadata.method = .leGallInteriorUnique then
        .square112ProfileTransport
      else
        .squareElementaryBoundary
  | .fourth .. =>
      if metadata.method = .leGallBoundary then
        .fourthElementaryBoundary
      else
        .fourthPositivePrescribedZOpen

def publicCoverageCount (tier : PublicCoverageTier) : Nat :=
  (componentMetadata.toList.filter fun metadata =>
    publicCoverageTier metadata = tier).length

/-! ## Exact positive fourth-row frontier -/
/-- The object ids of the genuinely recursive positive fourth-power rows,
in the same DFS order as the scalar ledger. -/
def positiveSixRegionObjectIds : List Nat :=
  (componentMetadata.toList.filter fun metadata ↦
    publicCoverageTier metadata =
      PublicCoverageTier.fourthPositivePrescribedZOpen).map
    ComponentMetadata.objectId

/-- The corresponding 21 literal grade triples, encoded by decimal digits
`100*i + 10*j + k` to keep the certificate computational. -/
def positiveSixRegionAddressCodes : List Nat :=
  (componentMetadata.toList.filter fun metadata ↦
    publicCoverageTier metadata =
      PublicCoverageTier.fourthPositivePrescribedZOpen).map fun metadata ↦
    match metadata.address with
    | .fourth i j k => 100 * i.val + 10 * j.val + k.val
    | _ => 0

/-- Exactly the 19 literal 022 ledger records have a published theorem whose
conclusion is already the required arbitrary-rational prescribed-Z value
predicate, with no tensor permutation or profile-transport lemma inserted. -/
def hasDirectPublicPrescribedZEndpoint
    (metadata : ComponentMetadata) : Bool :=
  publicCoverageTier metadata = .square022PrescribedZ

/-- Every other row still needs some bridge into its *own* literal basis,
distinguished Z-grading, and generated integer profile.  Many of these 161
rows already have stronger-looking scalar or exact-MM statements; this count
records precisely why those results do not by themselves discharge the
prescribed-Z premise used by the 181-node integration theorem. -/
def requiresPrescribedZBridge (metadata : ComponentMetadata) : Bool :=
  !hasDirectPublicPrescribedZEndpoint metadata

/-- `true` when the ledger profile is supported on one Z grade.  The six
atomic rows store `[0,0]` as a sentinel, but the 181-node integration replaces
that sentinel by `[1,0]`, so they are included here as one-hot profiles. -/
def hasOneHotLedgerZProfile (metadata : ComponentMetadata) : Bool :=
  metadata.method == .atomic ||
    (metadata.zCounts.filter (fun count => count != 0) ==
      [metadata.zDenominator])

/-- After setting aside both the direct 022 endpoint and the 40 one-hot
profiles, 121 genuinely nontrivial prescribed profiles still need a new
finite extraction/profile-transport argument. -/
def requiresNontrivialPrescribedZBridge
    (metadata : ComponentMetadata) : Bool :=
  requiresPrescribedZBridge metadata && !hasOneHotLedgerZProfile metadata

/-- The exact integer Z profiles obtainable from the public cyclic star family
have shape `[l, 2*g, l]` in the literal 112 orientation and
`[l+g, l+g, 0]` after either cyclic rotation puts an original X/Y mode in the
distinguished Z position. -/
def matchesPublicCyclicStarZShape (metadata : ComponentMetadata) : Bool :=
  match metadata.address, metadata.zCounts with
  | .square i j k, [a, b, c] =>
      if i.val = 1 ∧ j.val = 1 ∧ k.val = 2 then
        a == c && b % 2 == 0
      else if (i.val = 1 ∧ j.val = 2 ∧ k.val = 1) ∨
          (i.val = 2 ∧ j.val = 1 ∧ k.val = 1) then
        a == b && c == 0
      else
        false
  | _, _ => false

/-! ## Canonicalized cyclic profiles -/
/-- The first local id in a cyclic triple.  For all coupled rows the three
stored ids are consecutive, so their minimum identifies the literal `112`
anchor independently of orientation. -/
def cyclicTripleFirstLocalId (metadata : ComponentMetadata) : Nat :=
  min (metadata.rotationLocalIds 0)
    (min (metadata.rotationLocalIds 1) (metadata.rotationLocalIds 2))

/-- Recover the literal `112` member of a generated cyclic triple.  Coupled
square object ids are their one-based local ids plus six; outside that tier
the fallback is deliberately the input row. -/
def cyclic112Anchor (metadata : ComponentMetadata) : ComponentMetadata :=
  (componentMetadata.toList.find?
    (fun candidate ↦ candidate.objectId ==
      cyclicTripleFirstLocalId metadata + 6)).getD metadata

def isRetunedExceptionalCyclicTriple (metadata : ComponentMetadata) : Bool :=
  (cyclic112Anchor metadata).objectId == 76

def isDirectionalCyclicLanding (metadata : ComponentMetadata) : Bool :=
  match metadata.address with
  | .square i j k =>
      decide ((i.val = 1 ∧ j.val = 2 ∧ k.val = 1) ∨
        (i.val = 2 ∧ j.val = 1 ∧ k.val = 1))
  | _ => false

/-- The exact numerator `l` used by the public cyclic theorem.  Literal 112
rows normally use the sum of the two source edge counts, so that `l/(2D)` is
their average; object 76 is retuned to `l=1,g=4` (`p=1/10`).  Directional
121/211 rows use the common hidden source parameter `l=21,g=479`
(`p=21/1000`) whose Z pushforward is exactly half/half/zero. -/
def canonicalCyclicL (metadata : ComponentMetadata) : Nat :=
  if isDirectionalCyclicLanding metadata then 21
  else if isRetunedExceptionalCyclicTriple metadata then 1
  else
    (cyclic112Anchor metadata).zCounts[0]?.getD 0 +
      (cyclic112Anchor metadata).zCounts[2]?.getD 0

def canonicalCyclicG (metadata : ComponentMetadata) : Nat :=
  if isDirectionalCyclicLanding metadata then 479
  else if isRetunedExceptionalCyclicTriple metadata then 4
  else (cyclic112Anchor metadata).zDenominator - canonicalCyclicL metadata

/-- Snap the two 112 edge counts to their exact average, then use the exact
directional half/half/zero profile on both cyclic landings.  This is precisely
the integer family accepted by the public `f432e635` source theorem and the
`5fb56126` complete-profile-to-prescribed-Z adapter. -/
def canonicalCyclicZCounts (metadata : ComponentMetadata) : List Nat :=
  let l := canonicalCyclicL metadata
  let g := canonicalCyclicG metadata
  match metadata.address with
  | .square i j k =>
      if i.val = 1 ∧ j.val = 1 ∧ k.val = 2 then
        [l, 2 * g, l]
      else if (i.val = 1 ∧ j.val = 2 ∧ k.val = 1) ∨
          (i.val = 2 ∧ j.val = 1 ∧ k.val = 1) then
        [l + g, l + g, 0]
      else metadata.zCounts
  | _ => metadata.zCounts

def canonicalCyclicZDenominator (metadata : ComponentMetadata) : Nat :=
  if publicCoverageTier metadata = .square112ProfileTransport then
    2 * (canonicalCyclicL metadata + canonicalCyclicG metadata)
  else metadata.zDenominator

def hasCanonicalCyclicBalance (metadata : ComponentMetadata) : Bool :=
  decide (341 * canonicalCyclicL metadata <
    100 * canonicalCyclicG metadata)

def canonicalCyclicOrientationMatches (metadata : ComponentMetadata) : Bool :=
  let l := canonicalCyclicL metadata
  let g := canonicalCyclicG metadata
  match metadata.address with
  | .square a b c =>
      if a.val = 1 ∧ b.val = 1 ∧ c.val = 2 then
        canonicalCyclicZCounts metadata == [l, 2 * g, l]
      else if (a.val = 1 ∧ b.val = 2 ∧ c.val = 1) ∨
          (a.val = 2 ∧ b.val = 1 ∧ c.val = 1) then
        canonicalCyclicZCounts metadata == [l + g, l + g, 0]
      else false
  | _ => false

def CanonicalCyclicProfileShape (metadata : ComponentMetadata) : Prop :=
  let l := canonicalCyclicL metadata
  let g := canonicalCyclicG metadata
  match metadata.address with
  | .square a b c =>
      if a.val = 1 ∧ b.val = 1 ∧ c.val = 2 then
        canonicalCyclicZCounts metadata = [l, 2 * g, l]
      else if (a.val = 1 ∧ b.val = 2 ∧ c.val = 1) ∨
          (a.val = 2 ∧ b.val = 1 ∧ c.val = 1) then
        canonicalCyclicZCounts metadata = [l + g, l + g, 0]
      else False
  | _ => False

end MME.DWZFourthTensorLedger


