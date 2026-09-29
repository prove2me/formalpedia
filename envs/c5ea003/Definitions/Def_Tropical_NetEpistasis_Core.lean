-- Prove2me | Definitions.Def_Tropical_NetEpistasis_Core
-- name    : Tropical_NetEpistasis_Core
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:13.212119+00:00
-- url     : https://prove2.me/theorems/82c535b8-d850-457c-8bda-5be8f2b0abac
-- title:
--   Aether Catalog definitions — Tropical_NetEpistasis_Core
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.NetEpistasis.Core`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/NetEpistasis/Core.lean by skeleton subtraction
import Mathlib
/-
# Tropical pruning costs and layer epistasis — Core

A *prunable net* is a finite family of "computation paths".  Each path `i` uses a
finite set of layers `supp i` (the layers whose fine structure the path depends
on) and, if it survives, incurs a loss `loss i`.  Pruning a set `S` of layers
destroys exactly the paths whose support meets `S`; the network then falls back
on the best surviving path.  The resulting quantity

  `netLoss S = min { loss i | supp i ∩ S = ∅ }`

is a **min-plus (tropical) sum** over the surviving paths, and the *pruning cost*
of `S` is `cost S = netLoss S - netLoss ∅`.

This is the mathematical skeleton behind the NET-60 measurement
("THE-EPISTASIS-LIVES-IN-THE-TAIL-PAIR"): a per-layer sparsification budget
destroys some paths, and the accuracy drop is the increase of the tropical
minimum.  The point of the development is that the *joint* cost of two layers is
not determined by their solo costs; the deviation is the epistasis `epi`.

Main contents of this file:
* `NetEpistasis.PrunableNet`, `netLoss`, `cost`, `epi`;
* monotonicity and non-negativity of `cost`;
* `netLoss_eq_untrop_sum`: `netLoss` *is* a tropical sum in `Tropical (WithTop ℚ)`.
-/

namespace NetEpistasis

open Finset

/-- A finite path system on `n` layers.  `supp i` is the set of layers that path
`i` depends on, `loss i` is the loss the network incurs when path `i` is the best
surviving one.  `base` is a fallback path using no layer at all (a fully pruned
network still computes something), which guarantees that some path always
survives. -/
structure PrunableNet (n : ℕ) where
  /-- Index type of the paths. -/
  ι : Type
  [fintypeι : Fintype ι]
  [decEqι : DecidableEq ι]
  /-- Layers used by a path. -/
  supp : ι → Finset (Fin n)
  /-- Loss incurred by a path. -/
  loss : ι → ℚ
  /-- The fallback path. -/
  base : ι
  /-- The fallback path uses no layer. -/
  base_supp : supp base = ∅

attribute [instance] PrunableNet.fintypeι PrunableNet.decEqι

variable {n : ℕ} (N : PrunableNet n)

/-- The paths that survive pruning the layers in `S`. -/
def survivors (S : Finset (Fin n)) : Finset N.ι :=
  Finset.univ.filter fun i => Disjoint (N.supp i) S

variable {N}

@[simp] lemma mem_survivors {S : Finset (Fin n)} {i : N.ι} :
    i ∈ survivors N S ↔ Disjoint (N.supp i) S := by
  simp [survivors]

lemma base_mem_survivors (S : Finset (Fin n)) : N.base ∈ survivors N S := by
  simp [N.base_supp]

lemma survivors_nonempty (S : Finset (Fin n)) : (survivors N S).Nonempty :=
  ⟨N.base, base_mem_survivors S⟩


variable (N)

/-- The loss of the network after pruning the layers in `S`: the tropical
(min-plus) sum of the losses of the surviving paths. -/
noncomputable def netLoss (S : Finset (Fin n)) : ℚ :=
  (survivors N S).inf' (survivors_nonempty S) N.loss

/-- The pruning cost of a set of layers: the increase of the tropical minimum. -/
noncomputable def cost (S : Finset (Fin n)) : ℚ := netLoss N S - netLoss N ∅

/-- The setwise **epistasis**: the excess of the joint cost over the sum of the
individual costs.  Positive means super-additive. -/
noncomputable def epi (S T : Finset (Fin n)) : ℚ :=
  cost N (S ∪ T) - cost N S - cost N T

variable {N}













/-!
### The tropical identity

`netLoss` is literally a sum in the tropical semiring `Tropical (WithTop ℚ)`
(whose addition is `min`), taken over the surviving paths.
-/


end NetEpistasis


