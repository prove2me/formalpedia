-- Prove2me | solution 1 for MomentHierarchy.perm_pretransitive_offDiag
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-16T06:42:12.862602+00:00
-- url     : https://prove2.me/submissions/cce9da96-2103-44b3-b80b-4e6a85cc825e

/-
# `MomentHierarchy.perm_pretransitive_offDiag`
Target `ef9830a0-56a2-4169-a61e-1cee998aafce` (Open; re-read live immediately before submitting).

ORDINARY PROOF — chain screened: the TRANSITIVE closure of both preamble bundles
(`Def_Logic_MomentHierarchy`, `Def_Logic_MomentHierarchyBell`) contains NO `Theorems.` import,
so no `sorryAx` and no axiom audit.

BINDERS — three identical WA rejections state the expected type verbatim:

    has type     ∀ {X : Type ?u.4} [Finite X],                 IsPretransitive (Perm X) ↥(offDiagSub (Perm X) X)
    but expected ∀ (X : Type ?u.3) [Fintype X] [DecidableEq X], IsPretransitive (Perm X) ↥(offDiagSub (Perm X) X)

`X` EXPLICIT, `[Fintype X]` THEN `[DecidableEq X]`, and no `Group`/`MulAction` instances —
`Equiv.Perm X` supplies its own. Independently confirmed by the bundle source: the target sits at
L28, inside `section Symmetric`, whose only variable line is
`variable (X : Type*) [Fintype X] [DecidableEq X]` (Def_Logic_MomentHierarchyBell.lean:29).

MATHS. `offDiagSub` has carrier `{p : X × X | p.1 ≠ p.2}`, so an element hands us two distinct
points directly. The symmetric group is 2-pretransitive, which is exactly "any ordered pair of
distinct points goes to any other". No case split on `|X| ≤ 1` is needed: the two off-diagonal
elements are GIVEN, and their distinctness discharges the degenerate sizes on its own.

Verified by enumeration first: off-diagonal is empty for |X| ≤ 1 (vacuous) and a single orbit for
2 ≤ |X| ≤ 5.

PROBED, NOT GUESSED — read out of the vendored Mathlib source:
  * `Equiv.Perm.isMultiplyPretransitive (α : Type*) (n : ℕ) : IsMultiplyPretransitive (Perm α) α n`
    (`MultipleTransitivity.lean:522`) — NO instance arguments; the `[Finite ι]` it uses internally
    is on `Fin n`, which is automatic.
  * `MulAction.is_two_pretransitive_iff : IsMultiplyPretransitive G α 2 ↔
       ∀ {a b c d : α}, a ≠ b → c ≠ d → ∃ g : G, g • a = c ∧ g • b = d` (`:209`).
  * `SubMulAction.val_smul (r) (x) : (↑(r • x) : M) = r • (x : M)` (`SubMulAction.lean:121`).
-/
import Mathlib
import Definitions.Def_Logic_MomentHierarchy
import Definitions.Def_Logic_MomentHierarchyBell

set_option autoImplicit false
set_option maxHeartbeats 400000

open MulAction MomentHierarchy


/-- **The target, verbatim.** -/
theorem solution (X : Type*) [Fintype X] [DecidableEq X] :
    IsPretransitive (Equiv.Perm X) (offDiagSub (Equiv.Perm X) X) := by
  constructor
  intro p q
  -- the symmetric group is 2-pretransitive, for every n and with no finiteness needed
  have h2 : IsMultiplyPretransitive (Equiv.Perm X) X 2 :=
    Equiv.Perm.isMultiplyPretransitive X 2
  rw [MulAction.is_two_pretransitive_iff] at h2
  -- p.2 and q.2 ARE the distinctness facts the iff asks for
  obtain ⟨g, hg1, hg2⟩ := h2 p.2 q.2
  refine ⟨g, Subtype.ext ?_⟩
  rw [SubMulAction.val_smul]
  simp [Prod.ext_iff, hg1, hg2]
