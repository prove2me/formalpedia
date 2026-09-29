-- Prove2me | Definitions.Def_Bridges_ArgumentationKernelGame
-- name    : Bridges_ArgumentationKernelGame
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:12:07.930972+00:00
-- url     : https://prove2.me/theorems/650ac28d-3987-4073-8f09-fe6cbfc2ae0f
-- title:
--   Aether Catalog definitions — Bridges_ArgumentationKernelGame
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.ArgumentationKernelGame`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/ArgumentationKernelGame.lean by skeleton subtraction
import Mathlib

/-!
# Argumentation, kernels, and terminating games

A self-contained dictionary between stable extensions, graph kernels, and
normal-play P-positions.  The final section advances the dictionary from the
odd three-cycle obstruction to a positive four-cycle example.
-/

namespace ArgumentationKernelGame

variable {α : Type*}

/-- A set is independent and absorbs every vertex outside it. -/
def Kernel (R : α → α → Prop) (K : Set α) : Prop :=
  (∀ ⦃x⦄, x ∈ K → ∀ ⦃y⦄, y ∈ K → ¬ R x y) ∧
  (∀ ⦃x⦄, x ∉ K → ∃ y ∈ K, R x y)

/-- A conflict-free set attacking every argument outside it. -/
def Stable (R : α → α → Prop) (S : Set α) : Prop :=
  (∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → ¬ R x y) ∧
  (∀ ⦃x⦄, x ∉ S → ∃ y ∈ S, R y x)

/-- A consistent normal-play labelling by P-positions. -/
def GameSolution (R : α → α → Prop) (P : Set α) : Prop :=
  ∀ x, x ∈ P ↔ ∀ y, R x y → y ∉ P

/-
Stable semantics is precisely kernel semantics after reversing arrows.
-/

/-
Kernels are precisely consistent P-position solutions.
-/

/-
The three vocabularies therefore form one dictionary.
-/

/-
A position with no move belongs to every kernel.
-/

section WellFounded

variable (R : α → α → Prop) (hwf : WellFounded (flip R))

/-- The recursively defined predicate of losing positions. -/
noncomputable def isLoss : α → Prop :=
  hwf.fix fun x rec => ∀ y, ∀ h : R x y, ¬ rec y h

/-
The recursion equation for losing positions.
-/

/-
Recursive losing positions form a graph kernel.
-/




/-
A well-founded attack relation has exactly one stable extension.
-/

end WellFounded

section Cycles

/-- The directed three-cycle. -/
def cyc3 : Fin 3 → Fin 3 → Prop := fun x y =>
  (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨ (x = 2 ∧ y = 0)

/-
The directed three-cycle has no kernel.
-/

/-
Consequently the directed three-cycle has no stable extension.
-/

/-- The directed four-cycle. -/
def cyc4 : Fin 4 → Fin 4 → Prop := fun x y =>
  (x = 0 ∧ y = 1) ∨ (x = 1 ∧ y = 2) ∨
  (x = 2 ∧ y = 3) ∨ (x = 3 ∧ y = 0)

/-
The alternating vertices form a kernel of the even four-cycle.
-/

/-
Reversing the alternating kernel gives a stable extension of the four-cycle.
-/

/-
The four-cycle has two distinct stable extensions, unlike well-founded games.
-/

end Cycles

end ArgumentationKernelGame


