-- Prove2me | Definitions.Def_Shared_RainbowAPSpectrumMoments
-- name    : Shared_RainbowAPSpectrumMoments
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T15:06:10.674157+00:00
-- url     : https://prove2.me/theorems/9afea0af-c989-42db-a0d0-90cdf81d76a1
-- title:
--   Aether Catalog definitions — Shared_RainbowAPSpectrumMoments
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.RainbowAPSpectrumMoments`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/RainbowAPSpectrumMoments.lean by skeleton subtraction
import Mathlib

open Finset

namespace RainbowAP

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The set of colours of `α` that are missed by the word `f : Fin m → α`. -/
def missing {m : ℕ} (f : Fin m → α) : Finset α :=
  univ.filter (fun a => ∀ x, f x ≠ a)

/-- The number of colours missed by the word `f`. -/
def missCount {m : ℕ} (f : Fin m → α) : ℕ := (missing f).card








end RainbowAP


