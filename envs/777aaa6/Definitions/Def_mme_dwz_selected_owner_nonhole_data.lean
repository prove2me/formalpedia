-- Prove2me | Definitions.Def_mme_dwz_selected_owner_nonhole_data
-- name    : mme_dwz_selected_owner_nonhole_data
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-09-16T15:09:45.546596+00:00
-- url     : https://prove2.me/theorems/2ea9580c-eebb-41f8-9a58-42f5e2a17d7b
-- title:
--   Selected owners and uniquely compatible surviving blocks
-- statement:
--   Let W be a finite state space, A a finite target family contained in an ambient family B, and E_a the set of states retaining a. Each address has X and Y labels. At a state w, define S(w) to consist of retained targets a for which every retained ambient address sharing its X or Y label equals a.
--
--   Let U be a finite set of standard block indices, let e_a:U→Z transport blocks into an owner's coordinates, and let C(z,b) express compatibility with an owner. Define
--   $$
--   N_S(a)=\{u\in U: \forall b\in S,\ C(e_a(u),b)\Rightarrow b=a\}.
--   $$
--   Also define the competing targets for (a,u) to be the compatible members of A other than a. These definitions distinguish standard block indices from actual Z labels: no injectivity of e_a is built in. They provide a common interface for joint hash-state selection and coordinate-level tensor extraction.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5#S6.SS2, Section 6.2, Claim 6.8 and the subsequent Bounding the value argument; see also Section 6.1, Additional Zeroing-Out Steps 1 and 2. This is a finite event-counting bridge derived for the formalization, not a verbatim assertion of the paper.

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

set_option autoImplicit false
namespace MME.DWZOwnerMass

variable {State Edge Block X Y Z : Type*}
variable [Fintype State] [Nonempty State] [DecidableEq State]
variable [Fintype Edge] [DecidableEq Edge]
variable [Fintype Block] [DecidableEq Block]
variable [DecidableEq X] [DecidableEq Y]

def Isolated (ambient : Finset Edge) (events : Edge → Finset State)
    (x : Edge → X) (y : Edge → Y) (w : State) (a : Edge) : Prop :=
  ∀ b ∈ ambient, w ∈ events b → (x b = x a ∨ y b = y a) → b = a

noncomputable def selected (targets ambient : Finset Edge)
    (events : Edge → Finset State) (x : Edge → X) (y : Edge → Y)
    (w : State) : Finset Edge := by
  classical
  exact targets.filter (fun a ↦ w ∈ events a ∧ Isolated ambient events x y w a)

noncomputable def nonholes (owners : Finset Edge)
    (embed : Edge → Block → Z) (compatible : Z → Edge → Prop)
    (a : Edge) : Finset Block := by
  classical
  exact Finset.univ.filter (fun z ↦ ∀ b ∈ owners, compatible (embed a z) b → b = a)

noncomputable def competitors (targets : Finset Edge)
    (embed : Edge → Block → Z) (compatible : Z → Edge → Prop)
    (a : Edge) (z : Block) : Finset Edge := by
  classical
  exact targets.filter (fun b ↦ b ≠ a ∧ compatible (embed a z) b)

end MME.DWZOwnerMass


