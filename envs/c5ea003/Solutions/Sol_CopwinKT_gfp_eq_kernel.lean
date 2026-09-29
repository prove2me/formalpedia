-- Prove2me | solution 1 for CopwinKT.gfp_eq_kernel
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:20:54.38981+00:00
-- url     : https://prove2.me/submissions/d225d206-310b-4ec6-8865-10981c6707dd

-- Sol generated from Bridges/PosetTheory/CopwinKnasterTarski.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_CopwinKnasterTarski
/-
# A bridge: finite cop-win pruning ↔ Knaster–Tarski greatest fixed points

Implementations of the `k`-copwin recognition algorithm repeatedly *prune* a
finite candidate set of positions, deleting those that fail a local survival
test.  Two facts drive every such implementation:

* each round returns a **subset** of the current state space (the update is
  *contracting*), and
* refining the input can only refine the output (the update is *monotone*).

Under these two hypotheses the algorithm terminates and returns a distinguished
fixed candidate set.  This file proves that this *algorithmic* object is exactly
an *order-theoretic* object from lattice theory: the **greatest fixed point**
(à la Knaster–Tarski) of an associated monotone endomorphism of the complete
lattice `Set α`.

This is a genuine cross-domain bridge:

* **Left side (combinatorics / algorithm termination).**  A contracting update
  `F : Finset α → Finset α` iterated by `rounds` reaches a fixed point in at
  most `|S|` steps (`exists_fixed_round_le_card`), and that fixed point is the
  greatest fixed candidate set below `S` (`exists_greatest_fixed_kernel`).

* **Right side (order theory / fixed-point theory).**  On the complete lattice
  `Set α`, the map `G F S` is a bona fide `OrderHom`, and Mathlib's
  `OrderHom.gfp` gives its greatest fixed point via Knaster–Tarski.

* **The bridge.**  `gfp_eq_kernel` shows the coercion of the algorithmic kernel
  equals `OrderHom.gfp (G F S)`, and `gfp_computed_by_finite_iteration`
  strengthens this to: the abstract greatest fixed point is *computed* by the
  concrete finite pruning loop within `|S|` rounds.

The file is self-contained (depends only on Mathlib).
-/


open Classical Finset

open CopwinKT

variable {α : Type*}

/-! ### The algorithmic side: finite pruning -/










/-! ### The order-theoretic side: a monotone map on the complete lattice `Set α` -/


@[simp] lemma G_apply (F : Finset α → Finset α) (S : Finset α) (hmono : MonotoneUpdate F)
    (X : Set α) : G F S hmono X = ↑(F (S.filter (fun a => a ∈ X))) := rfl

/-- On a fixed kernel `T ⊆ S`, the lattice map `G` fixes `↑T`. -/
lemma G_fixes_kernel (F : Finset α → Finset α) (S : Finset α) (hmono : MonotoneUpdate F)
    {T : Finset α} (hTS : T ⊆ S) (hfix : F T = T) :
    G F S hmono (↑T) = ↑T := by
  have hfilt : S.filter (fun a => a ∈ (↑T : Set α)) = T := by
    ext a
    rw [Finset.mem_filter, Finset.mem_coe]
    exact ⟨fun h => h.2, fun h => ⟨hTS h, h⟩⟩
  rw [G_apply, Finset.filter_congr_decidable, hfilt, hfix]

/-! ### The bridge -/



/-! ### A concrete instance -/



open CopwinKT in
theorem solution(F : Finset α → Finset α) (hcontract : Contracting F)
    (hmono : MonotoneUpdate F) (S : Finset α)
    {K : Finset α} (hKS : K ⊆ S) (hKfix : F K = K)
    (hKmax : ∀ T ⊆ S, F T = T → T ⊆ K) :
    OrderHom.gfp (G F S hmono) = (↑K : Set α) := by
  apply le_antisymm
  · -- `gfp ≤ ↑K`: any post-fixed point `b` lives below `↑S`, hence is `↑T` for a
    -- finite `T ⊆ S` which is an `F`-fixed point, hence contained in `K`.
    apply OrderHom.gfp_le
    intro b hb
    have hbS : b ⊆ (↑S : Set α) := by
      refine hb.trans ?_
      rw [G_apply]; exact_mod_cast (hcontract _).trans (Finset.filter_subset _ _)
    set T := S.filter (fun a => a ∈ b) with hT
    have hTS : T ⊆ S := Finset.filter_subset _ _
    have hbT : b = (↑T : Set α) := by
      rw [hT]; ext a
      simp only [Finset.coe_filter, Set.mem_setOf_eq]
      exact ⟨fun ha => ⟨hbS ha, ha⟩, fun ha => ha.2⟩
    have hGb : G F S hmono b = ↑(F T) := by rw [G_apply, Finset.filter_congr_decidable, ← hT]
    have hbFT : b ⊆ (↑(F T) : Set α) := hGb ▸ hb
    have hTFT : T ⊆ F T := by rw [hbT] at hbFT; exact_mod_cast hbFT
    have hFTeq : F T = T := Finset.Subset.antisymm (hcontract _) hTFT
    rw [hbT]; exact_mod_cast hKmax T hTS hFTeq
  · -- `↑K ≤ gfp`: `↑K` is itself a fixed point of `G`.
    apply OrderHom.le_gfp
    rw [G_fixes_kernel F S hmono hKS hKfix]
