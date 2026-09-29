-- Prove2me | Definitions.Def_Logic_Logic_ProjectiveFraisseInvLimit
-- name    : Logic_Logic_ProjectiveFraisseInvLimit
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:56:15.107302+00:00
-- url     : https://prove2.me/theorems/a412b874-715e-42a8-8663-71f706a0102b
-- title:
--   Aether Catalog definitions — Logic_Logic_ProjectiveFraisseInvLimit
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.Logic.ProjectiveFraisseInvLimit`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/Logic/ProjectiveFraisseInvLimit.lean by skeleton subtraction
import Mathlib

/-!
# Inverse limits of sequences of topological spaces

This file develops a small amount of theory about the inverse (projective) limit of a
sequence of topological spaces `F : ℕ → Type*` connected by bonding maps
`bond n : F (n+1) → F n`.

We define the underlying set `invLimitSet bond` of coherent sequences and the subtype
`InvLimit F bond`, and prove:

* `isClosed_invLimit`: the inverse limit is closed when each `F n` is Hausdorff and the
  bonding maps are continuous;
* `nonempty_invLimit`: the inverse limit is nonempty when each `F n` is nonempty and the
  bonding maps are surjective;
* `compactSpace_invLimit`: the inverse limit is compact when each `F n` is compact Hausdorff
  and the bonding maps are continuous.
-/

universe u

variable {F : ℕ → Type u} [∀ n, TopologicalSpace (F n)]

/-- The set of coherent sequences for the bonding maps `bond`. -/
def invLimitSet (bond : ∀ n, F (n+1) → F n) : Set (∀ n, F n) :=
  {x | ∀ n, bond n (x (n+1)) = x n}

/-- The inverse limit of the sequence `F` with bonding maps `bond`, as a subtype. -/
def InvLimit (F : ℕ → Type u) [∀ n, TopologicalSpace (F n)]
    (bond : ∀ n, F (n+1) → F n) : Type u :=
  {x // x ∈ invLimitSet bond}

instance instTopologicalSpaceInvLimit (bond : ∀ n, F (n+1) → F n) :
    TopologicalSpace (InvLimit F bond) :=
  inferInstanceAs (TopologicalSpace {x // x ∈ invLimitSet bond})

/-- The inverse limit is a closed subset of the product when each space is Hausdorff and the
bonding maps are continuous. -/
theorem isClosed_invLimit [∀ n, T2Space (F n)] (bond : ∀ n, F (n+1) → F n)
    (hbond : ∀ n, Continuous (bond n)) : IsClosed (invLimitSet bond) := by
  have : invLimitSet bond = ⋂ n, {x : ∀ n, F n | bond n (x (n+1)) = x n} := by
    ext x; simp [invLimitSet]
  rw [this]
  refine isClosed_iInter (fun n => ?_)
  have hcont : Continuous (fun x : ∀ n, F n => (bond n (x (n+1)), x n)) :=
    ((hbond n).comp (continuous_apply (n+1))).prodMk (continuous_apply n)
  have : {x : ∀ n, F n | bond n (x (n+1)) = x n}
      = (fun x : ∀ n, F n => (bond n (x (n+1)), x n)) ⁻¹' {p : F n × F n | p.1 = p.2} := rfl
  rw [this]
  exact (isClosed_diagonal).preimage hcont


/-- The inverse limit of a sequence of compact Hausdorff spaces is compact. -/
instance compactSpace_invLimit [∀ n, CompactSpace (F n)] [∀ n, T2Space (F n)]
    (bond : ∀ n, F (n+1) → F n) (hbond : ∀ n, Continuous (bond n)) :
    CompactSpace (InvLimit F bond) := by
  have hcl : IsClosed (invLimitSet bond) := isClosed_invLimit bond hbond
  exact isCompact_iff_compactSpace.mp (hcl.isCompact)


