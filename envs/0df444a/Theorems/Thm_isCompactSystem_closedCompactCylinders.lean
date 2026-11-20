-- Prove2me | Theorems.Thm_isCompactSystem_closedCompactCylinders
-- name    : isCompactSystem_closedCompactCylinders
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T07:27:08.531801+00:00
-- url     : https://prove2.me/theorems/470f7621-f1e7-4b32-b1f6-718348555235
-- title:
--   isCompactSystem closedCompactCylinders
-- statement:
--   The source theorem `isCompactSystem_closedCompactCylinders` is extracted from `KolmogorovExtension4.CompactSystem`. The original Lean proposition is retained verbatim, and its proof is tracked separately for remote certification.
-- source:
--   https://github.com/cgarryZA/LevyStochCalc

import Definitions.Def_KolmogorovExtension4_CompactSystem_F000

/-
Copyright (c) 2023 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Peter Pfaffelhuber
-/

@[expose] public section

open Set MeasureTheory

section definition

variable {α : Type*} {p : Set α → Prop} {C : ℕ → Set α}

end definition

section ClosedCompactCylinders

/-! We prove that the `closedCompactCylinders` are a compact system. -/

variable {ι : Type*} {α : ι → Type*} [∀ i, TopologicalSpace (α i)] {s : ℕ → Set (Π i, α i)}

local notation "Js" => closedCompactCylinders.finset
local notation "As" => closedCompactCylinders.set

section AllProj

end AllProj

section projCylinder

end projCylinder

section piCylinderSet

end piCylinderSet

theorem isCompactSystem_closedCompactCylinders : IsCompactSystem (closedCompactCylinders α) := by sorry
