-- Prove2me | solution 1 for Z2SuspensionTower.nonempty_iff_exists_pos
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T06:16:40.43532+00:00
-- url     : https://prove2.me/submissions/86954da9-ef55-4283-9e6f-16abb148697c

-- Sol generated from Novelty/Z2CoindexSuspensionTower.lean
import Mathlib
import Definitions.Def_Novelty_Z2CoindexSuspensionTower
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# The suspension tower and the *exact* ℤ₂-coindex of combinatorial spheres

This file is a self-contained *deepening* of the constructive lower-bound results on the
`ℤ₂`-coindex under suspension.  A companion development proved the lower bound
`m ≤ n → Nonempty (Z2Map m n)` (i.e. `coind(Sⁿ) ≥ n`) and the matching upper bound
`IsEmpty (Z2Map (n+1) n)` **only** in the two base cases `n = 0, 1` (by `decide`).  Here we prove the
upper bound **in every dimension**, obtaining the exact value of the coindex and a sharp description
of the whole suspension tower.

## The model (recalled, self-contained)

The `n`-dimensional combinatorial sphere `Sⁿ` is the boundary of the `(n+1)`-cross-polytope; its
vertices are the signed unit vectors `±eᵢ`, encoded as `SVert n := Fin (n+1) × Bool`.  The free
`ℤ₂`-action is the antipodal map `anti (i, b) = (i, !b)`.  A `ℤ₂`-map `Sᵐ → Sⁿ` (`Z2Map m n`) is a
simplicial, antipodally-equivariant vertex map; simpliciality has the local form "no two
non-antipodal vertices map to an antipodal pair".

## The combinatorial heart

A `ℤ₂`-map is equivariant, so it is determined by the images of the positive vertices `(i, true)`
(`nonempty_iff_exists_pos`).  Writing that data as `g : Fin (m+1) → SVert n` and its *coordinate*
part `σ i = (g i).1`, simpliciality of the induced map is **equivalent to `σ` being injective**
(`induced_simplicial_iff_injective`).  Geometrically: a simplicial antipodal map of cross-polytopes
can only inject coordinate axes (with independent signs), so it exists exactly when there are enough
target axes.

## Main results

* `induced_simplicial_iff_injective` — simpliciality `⇔` injectivity of the coordinate map.
* `nonempty_iff_le` : `Nonempty (Z2Map m n) ↔ m ≤ n` — the **exact** criterion (Borsuk–Ulam upper
  bound and constructive lower bound in one statement).
* `borsuk_ulam_general` : `IsEmpty (Z2Map (n+1) n)` for **all** `n` — the full Borsuk–Ulam upper
  bound `coind(Sⁿ) ≤ n`.
* `coind`, `coind_eq` : `coind(Sⁿ) := sSup {m | Nonempty (Z2Map m n)}` equals `n`.
* `Z2Map.suspIter` : the `k`-fold suspension functor `Z2Map m n → Z2Map (m+k) (n+k)`.
* `suspension_tower_raises_coindex`, `suspension_tower_exact` : the tower raises the coindex bound by
  exactly `k`; `Nonempty (Z2Map (m+k) (n+k)) ↔ Nonempty (Z2Map m n)`, so suspension preserves the
  "excess" `n - m`.
* `borsuk_ulam_tower_sharp` : `IsEmpty (Z2Map (n+k+1) (n+k))` — every level of the tower is
  Borsuk–Ulam sharp.
-/

open Z2SuspensionTower

open Function

/-! ## Vertices of the combinatorial sphere and the antipodal action -/





/-! ## ℤ₂-maps of combinatorial spheres -/


open Z2Map


/-! ### The suspension functor on maps -/










/-! ## Decidable / finite reformulation via positive-vertex data -/




/-! ## Simpliciality of the induced map is injectivity of the coordinate map -/



/-! ## The exact coindex criterion -/



/-! ## The exact coindex -/



/-! ## The suspension tower -/







open Z2SuspensionTower in
theorem solution(m n : ℕ) :
    Nonempty (Z2Map m n) ↔
      ∃ g : Fin (m + 1) → SVert n,
        ∀ p q, induced g p = anti (induced g q) → p = anti q := by
  constructor
  · rintro ⟨F⟩
    refine ⟨fun i => F.toFun (i, true), ?_⟩
    have hface : induced (fun i => F.toFun (i, true)) = F.toFun := by
      funext p
      obtain ⟨i, b⟩ := p
      cases b with
      | true => rfl
      | false => exact (F.equiv (i, true)).symm
    rw [hface]; exact F.simpl
  · rintro ⟨g, hg⟩
    exact ⟨⟨induced g, induced_equiv g, hg⟩⟩
