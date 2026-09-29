-- Prove2me | Definitions.Def_MachineLearning_Consciousness_GlobalWorkspace
-- name    : MachineLearning_Consciousness_GlobalWorkspace
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T18:39:34.179984+00:00
-- url     : https://prove2.me/theorems/20bdfc4b-c1b2-4fe1-a963-ea33c1dd22cb
-- title:
--   Aether Catalog definitions — MachineLearning_Consciousness_GlobalWorkspace
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.Consciousness.GlobalWorkspace`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/Consciousness/GlobalWorkspace.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.MachineLearning.Consciousness.GlobalWorkspace

Auto-generated from theorem catalog database.
Domain: MachineLearning/Consciousness
Declarations: 7
-/


/-- A processor in the global workspace architecture -/
structure GWProcessor where
  LocalState : Type
  Domain : Type
  process : LocalState → LocalState
  relevance : LocalState → ℝ








/-- The global workspace: a broadcast channel -/
structure GlobalWorkspace (n : ℕ) where
  Content : Type
  processors : Fin n → GWProcessor
  currentContent : Content
  broadcast : Content → Fin n → GWProcessor → GWProcessor




/-- The ignition event: when a coalition wins and broadcasts -/
structure Ignition (n : ℕ) where
  workspace : GlobalWorkspace n
  content : workspace.Content
  global_access : ∀ i : Fin n, True








/-- The "spotlight of attention" selects content for the global workspace. -/
structure Spotlight where
  Contents : Type
  inSpotlight : Contents → Prop
  narrow : ∃ c, ¬ inSpotlight c
  nonempty : ∃ c, inSpotlight c


