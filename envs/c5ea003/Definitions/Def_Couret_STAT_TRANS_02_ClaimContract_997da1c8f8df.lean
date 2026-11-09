-- Prove2me | Definitions.Def_Couret_STAT_TRANS_02_ClaimContract_997da1c8f8df
-- name    : Couret_STAT_TRANS_02_ClaimContract_997da1c8f8df
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:25.661938+00:00
-- url     : https://prove2.me/theorems/a764f706-80ef-4173-983a-93a54b3adac6
-- title:
--   Claim metadata, transport receipts, and invalidation deltas
-- statement:
--   Within CouretOaiBridge01.StatusTransport, Metadata contains eight independent string fields: epistemic, novelty, quality, provenance, diffusion, lifecycle, workflow, and version. ClaimContract α combines a semantic Claim α, that metadata, and a list of string dependencies. AxisChange is either unchanged or witnessed by a string. AxisJustified requires equality of source and target strings for unchanged and is True for every witnessed label, including an empty label. ContractTransport source target includes semantic Transport, a change declaration and matching justification for each metadata field, plus a dependency declaration that requires list equality only when unchanged. Delta records ten Boolean change flags, all defaulting to false. Semantic invalidation reads only semanticChanged; replay invalidation is the disjunction of semantic, quality, version, and dependency changes; novelty invalidation is semanticChanged or noveltyChanged. These structures record witnesses and policy choices without authenticating labels or proving that a changed metadata value is scientifically justified.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/STAT_TRANS_02_ClaimContract.lean; source file SHA-256 2ce737b67669cb763530ea9c85c4f876ca1339f8a5f73803b724ea5cf51fc113

import Mathlib.Data.Set.Basic
import Definitions.Def_Couret_STAT_TRANS_01_StatusTransport_83d60d1e5141

/-!
# STAT-TRANS-02 — Multidimensional Claim Contract transport

This file extends STAT-TRANS-01 without collapsing epistemic, novelty,
reproducibility, provenance, diffusion, lifecycle, workflow, or version into
one score.

A changed axis must be accompanied by a witness label.  An unchanged axis
must be propositionally equal between source and target.

This is a minimal typed governance kernel.  It does not claim that witness
labels are themselves mathematically sufficient; later layers may replace
String labels by stronger certificate types.

No RH claim. No novelty claim.
-/

namespace CouretOaiBridge01
namespace StatusTransport

/-- Orthogonal metadata carried by a scientific claim contract. -/
structure Metadata where
  epistemic : String
  novelty : String
  quality : String
  provenance : String
  diffusion : String
  lifecycle : String
  workflow : String
  version : String
  deriving Repr, DecidableEq

/-- A semantic claim plus orthogonal metadata and explicit dependencies. -/
structure ClaimContract (α : Type*) where
  semantic : Claim α
  metaInfo : Metadata
  deps : List String

/-- An axis is either unchanged or changed under an explicit witness label. -/
inductive AxisChange where
  | unchanged
  | witnessed (receipt : String)
  deriving Repr, DecidableEq

/-- The change declaration is compatible with source and target axis values. -/
def AxisJustified (source target : String) : AxisChange → Prop
  | .unchanged => source = target
  | .witnessed _ => True

/-- A multidimensional transport receipt. -/
structure ContractTransport {α : Type*}
    (source target : ClaimContract α) where
  semantic : Transport source.semantic target.semantic
  epistemicChange : AxisChange
  noveltyChange : AxisChange
  qualityChange : AxisChange
  provenanceChange : AxisChange
  diffusionChange : AxisChange
  lifecycleChange : AxisChange
  workflowChange : AxisChange
  versionChange : AxisChange
  dependencyReceipt : AxisChange
  epistemicOk :
    AxisJustified source.metaInfo.epistemic target.metaInfo.epistemic epistemicChange
  noveltyOk :
    AxisJustified source.metaInfo.novelty target.metaInfo.novelty noveltyChange
  qualityOk :
    AxisJustified source.metaInfo.quality target.metaInfo.quality qualityChange
  provenanceOk :
    AxisJustified source.metaInfo.provenance target.metaInfo.provenance provenanceChange
  diffusionOk :
    AxisJustified source.metaInfo.diffusion target.metaInfo.diffusion diffusionChange
  lifecycleOk :
    AxisJustified source.metaInfo.lifecycle target.metaInfo.lifecycle lifecycleChange
  workflowOk :
    AxisJustified source.metaInfo.workflow target.metaInfo.workflow workflowChange
  versionOk :
    AxisJustified source.metaInfo.version target.metaInfo.version versionChange
  dependenciesOk :
    match dependencyReceipt with
    | .unchanged => source.deps = target.deps
    | .witnessed _ => True











/-- A compact delta used by differential invalidation. -/
structure Delta where
  semanticChanged : Bool := false
  epistemicChanged : Bool := false
  noveltyChanged : Bool := false
  qualityChanged : Bool := false
  provenanceChanged : Bool := false
  diffusionChanged : Bool := false
  lifecycleChanged : Bool := false
  workflowChanged : Bool := false
  versionChanged : Bool := false
  dependenciesChanged : Bool := false
  deriving Repr, DecidableEq

/-- Mathematical truth transport must be reconsidered after semantic change. -/
def Delta.invalidatesSemantic (δ : Delta) : Bool :=
  δ.semanticChanged

/--
Replay quality is invalidated by semantic, quality, version, or dependency
changes, but not merely by novelty or diffusion updates.
-/
def Delta.invalidatesReplay (δ : Delta) : Bool :=
  δ.semanticChanged || δ.qualityChanged || δ.versionChanged ||
    δ.dependenciesChanged

/-- Novelty audit is affected only by novelty or semantic changes. -/
def Delta.invalidatesNovelty (δ : Delta) : Bool :=
  δ.semanticChanged || δ.noveltyChanged









end StatusTransport
end CouretOaiBridge01


