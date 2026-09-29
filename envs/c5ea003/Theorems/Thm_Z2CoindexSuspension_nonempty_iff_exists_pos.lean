-- Prove2me | Theorems.Thm_Z2CoindexSuspension_nonempty_iff_exists_pos
-- name    : Z2CoindexSuspension.nonempty_iff_exists_pos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:41:25.803397+00:00
-- url     : https://prove2.me/theorems/5aed85ea-2e98-4711-add6-15bb3db2268d
-- title:
--   `Nonempty (Z2Map m n)` is equivalent to the existence of positive-vertex data whose
-- statement:
--   `Nonempty (Z2Map m n)` is equivalent to the existence of positive-vertex data whose
--   induced map is simplicial.  As `SVert n` and `Fin (m+1)` are finite, the right-hand side is
--   decidable, so this reduces existence of a `ℤ₂`-map to a finite check.
--
--   ```lean
--   theorem Z2CoindexSuspension.nonempty_iff_exists_pos(m n : ℕ) :
--       Nonempty (Z2Map m n) ↔
--         ∃ g : Fin (m + 1) → SVert n,
--           ∀ p q, induced g p = anti (induced g q) → p = anti q := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/Z2CoindexSuspension.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/Z2CoindexSuspension.lean#L239

-- Thm stub generated from Novelty/Z2CoindexSuspension.lean
import Mathlib
import Definitions.Def_Novelty_Z2CoindexSuspension
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic)
-/

/-!
# The ℤ₂-coindex under suspension: the constructive lower-bound half

This file develops a fully combinatorial, self-contained model of *free `ℤ₂`-complexes*
via the boundary complexes of cross-polytopes (the "octahedral" combinatorial spheres)
and proves, **unconditionally**, the constructive lower-bound half of the behaviour of the
`ℤ₂`-coindex under suspension.

## The model

The `n`-dimensional combinatorial sphere `Sⁿ` is the boundary of the `(n+1)`-dimensional
cross-polytope.  Its vertices are the signed unit vectors `±eᵢ`, `i = 0, …, n`, which we
encode as `SVert n := Fin (n+1) × Bool`: the pair `(i, b)` is the vector `+eᵢ` when
`b = true` and `-eᵢ` when `b = false`.  The free `ℤ₂`-action is the *antipodal map*
`anti (i, b) = (i, !b)`, which is a fixed-point-free involution (`anti_anti`, `anti_ne`).

A **`ℤ₂`-map** `Sᵐ → Sⁿ` (`Z2Map m n`) is a *simplicial* map of the boundary complexes that
commutes with the antipodal action.  Because a simplex of the cross-polytope is exactly a
set of vertices containing **no antipodal pair**, the simpliciality condition has a clean
purely local (vertex-pair) form:

* `equiv` : `f (anti p) = anti (f p)` (`ℤ₂`-equivariance);
* `simpl` : `f p = anti (f q) → p = anti q` (no two non-antipodal vertices are sent to an
  antipodal pair — equivalently, faces map to faces).

## Main results

* `Z2Map.id`, `Z2Map.comp` — the `ℤ₂`-maps form a category (identity and composition).
* `Z2Map.incl : Z2Map n (n+1)` — the equatorial inclusion `Sⁿ ↪ Sⁿ⁺¹`.
* `Z2Map.susp : Z2Map m n → Z2Map (m+1) (n+1)` — the **suspension functor** on maps: a
  `ℤ₂`-map `Sᵐ → Sⁿ` suspends to a `ℤ₂`-map `Sᵐ⁺¹ → Sⁿ⁺¹`.  This is the geometric heart of
  the constructive lower bound.
* `coindex_lower_bound` — the **constructive lower-bound half**: `m ≤ n → Nonempty (Z2Map m n)`,
  i.e. `coind(Sⁿ) ≥ n`.
* `suspension_raises_coindex` — `Nonempty (Z2Map m n) → Nonempty (Z2Map (m+1) (n+1))`: the
  coindex bound provided by suspension increases by (at least) one, constructively.
* `nonempty_iff_exists_pos` — a decidable reformulation of `Nonempty (Z2Map m n)` in terms of
  the finite data of the images of the positive vertices.
* `borsuk_ulam_S1_S0` : `IsEmpty (Z2Map 1 0)` — there is **no** `ℤ₂`-map `S¹ → S⁰`.
* `borsuk_ulam_S2_S1` : `IsEmpty (Z2Map 2 1)` — there is **no** `ℤ₂`-map `S² → S¹`.
  These two are genuine finite instances of the Borsuk–Ulam theorem, verified by `decide`
  over the finite reformulation; they show the lower bound `coind(Sⁿ) = n` is *sharp* at the
  bottom of the tower, hence the suspension increment is exactly one.

Together these results establish, unconditionally, the constructive lower-bound half of the
maximal-excess programme for free `ℤ₂`-complexes: suspension raises the coindex, the increase
is realised by an explicit suspended map, and the resulting bound is sharp in the base cases.

The matching *upper* bound `coind(Sⁿ) ≤ n` in every dimension is the full strength of the
Borsuk–Ulam / Tucker theorem and is not proved here (only its finite base instances are).
-/

open Z2CoindexSuspension

/-! ## Vertices of the combinatorial sphere and the antipodal action -/










/-! ## ℤ₂-maps of combinatorial spheres -/


open Z2Map











/-! ## The constructive lower bound and the suspension increment -/




/-! ## Decidable reformulation via positive-vertex data -/

theorem Z2CoindexSuspension.nonempty_iff_exists_pos(m n : ℕ) :
    Nonempty (Z2Map m n) ↔
      ∃ g : Fin (m + 1) → SVert n,
        ∀ p q, induced g p = anti (induced g q) → p = anti q := by sorry
