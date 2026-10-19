-- Prove2me | Definitions.Def_AT260939824_Actions
-- name    : AT260939824_Actions
-- status  : Definition
-- author  : @username
-- created : 2026-10-19T02:40:52.422864+00:00
-- url     : https://prove2.me/theorems/1ec64f6d-68c4-436f-9d59-1fb471b524c9
-- title:
--   The free binary lattice shift
-- statement:
--   For a dimension $d$, let $G=\mathbb Z^d$. A binary configuration is a function $x:G\to\{0,1\}$, with product topology and translation action
--
--   $$ (g\cdot x)(u)=x(u+g). $$
--
--   The free part consists of configurations with no nonzero translation period and carries the induced topology and action. Both shift actions are continuous. These definitions provide the canonical free shift space used to compare continuous graph-homomorphism problems.
-- source:
--   Ruijun Wang, Continuous graph homomorphisms of higher dimensional abelian group actions, arXiv:2609.39824v1 (2026), Section(s) 2.1; https://arxiv.org/abs/2609.39824v1. This item is auxiliary infrastructure of the accompanying formalization, not a claim that each implementation definition is separately numbered in the paper. Original Lean module AbelianTargets/Actions.lean, selected declaration lines 77, 79-80, 82-91, 93-94, 96-97, 99-117, 123-127, 129-130, 132-137; SHA-256 3e8b028f76937fdf3eeee4a2dfb08bb545fe5f1011b04bfd1976beaaf1a37c0c. Selected spans are from the final generated manifest. The original source snapshot is local; no public repository URL or commit was available.

import Definitions.Def_AbelianTargets260939824Actions
import Init
import Mathlib.Algebra.Group.Action.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.Separation.Profinite

set_option autoImplicit false

/-!
Definitions for arXiv:2609.39824v1, Sections 2.1 and 7.2.
The action convention is `(g +ᵥ x)(u) = x(u + g)`.
-/

namespace AbelianTargets























abbrev ShiftSpace (d : ℕ) := Lattice d → Bool

def shift {d : ℕ} (g : Lattice d) (x : ShiftSpace d) : ShiftSpace d :=
  fun u => x (u + g)

instance shiftAction (d : ℕ) : AddAction (Lattice d) (ShiftSpace d) where
  vadd := shift
  zero_vadd x := by
    change shift 0 x = x
    ext u
    simp [shift]
  add_vadd g h x := by
    change shift (g + h) x = shift g (shift h x)
    ext u
    simp [shift, add_comm, add_left_comm]

def FreeShift (d : ℕ) :=
  {x : ShiftSpace d // ∀ g : Lattice d, shift g x = x → g = 0}

instance freeShiftTopology (d : ℕ) : TopologicalSpace (FreeShift d) :=
  TopologicalSpace.induced (fun x : FreeShift d => x.val) inferInstance

instance freeShiftAction (d : ℕ) : AddAction (Lattice d) (FreeShift d) where
  vadd g x := ⟨shift g x.val, by
    intro h hh
    apply x.property h
    funext u
    have hp := congrFun hh (u - g)
    change x.val ((u - g + h) + g) = x.val ((u - g) + g) at hp
    rw [add_right_comm (u - g) h g, sub_add_cancel] at hp
    exact hp⟩
  zero_vadd x := by
    apply Subtype.ext
    change shift 0 x.val = x.val
    ext u
    simp [shift]
  add_vadd g h x := by
    apply Subtype.ext
    change shift (g + h) x.val = shift g (shift h x.val)
    ext u
    simp [shift, add_comm, add_left_comm]



theorem continuous_shift {d : ℕ} (g : Lattice d) :
    Continuous (shift g : ShiftSpace d → ShiftSpace d) := by
  apply continuous_pi
  intro u
  exact continuous_apply (u + g)

instance shiftContinuousVAdd (d : ℕ) : ContinuousVAdd (Lattice d) (ShiftSpace d) where
  continuous_vadd := continuous_prod_of_discrete_left.mpr (fun g => continuous_shift g)

instance freeShiftContinuousVAdd (d : ℕ) : ContinuousVAdd (Lattice d) (FreeShift d) where
  continuous_vadd := by
    apply continuous_induced_rng.mpr
    have hf : Continuous (fun x : FreeShift d => x.val) := continuous_induced_dom
    exact (continuous_vadd (M := Lattice d) (X := ShiftSpace d)).comp
      (continuous_fst.prodMk (hf.comp continuous_snd))





end AbelianTargets


