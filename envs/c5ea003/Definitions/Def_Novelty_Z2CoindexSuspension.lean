-- Prove2me | Definitions.Def_Novelty_Z2CoindexSuspension
-- name    : Novelty_Z2CoindexSuspension
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:54:23.647637+00:00
-- url     : https://prove2.me/theorems/51f51e54-9a96-44c9-b32c-13851e0ef145
-- title:
--   Aether Catalog definitions — Novelty_Z2CoindexSuspension
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Z2CoindexSuspension`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Z2CoindexSuspension.lean by skeleton subtraction
import Mathlib
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

namespace Z2CoindexSuspension

/-! ## Vertices of the combinatorial sphere and the antipodal action -/

/-- Vertices of the `n`-dimensional combinatorial sphere `Sⁿ` (the boundary of the
`(n+1)`-cross-polytope): `(i, b)` encodes the signed unit vector `±eᵢ`. -/
abbrev SVert (n : ℕ) := Fin (n + 1) × Bool

/-- The antipodal map, the free `ℤ₂`-action `±eᵢ ↦ ∓eᵢ`. -/
def anti {n : ℕ} (p : SVert n) : SVert n := (p.1, !p.2)




/-- The suspension of a vertex: reuse the same index in the enlarged sphere `Sⁿ⁺¹`. -/
def suspV {n : ℕ} (p : SVert n) : SVert (n + 1) := (p.1.castSucc, p.2)

lemma suspV_anti {n : ℕ} (p : SVert n) : suspV (anti p) = anti (suspV p) := by
  simp [suspV, anti]



/-! ## ℤ₂-maps of combinatorial spheres -/

/-- A `ℤ₂`-map of combinatorial spheres `Sᵐ → Sⁿ`: a simplicial map of the cross-polytope
boundary complexes that commutes with the antipodal action. -/
structure Z2Map (m n : ℕ) where
  /-- The underlying vertex map. -/
  toFun : SVert m → SVert n
  /-- Equivariance with respect to the antipodal `ℤ₂`-action. -/
  equiv : ∀ p, toFun (anti p) = anti (toFun p)
  /-- Simpliciality: two vertices land on an antipodal pair only if they were antipodal
  (so faces — antipodal-pair-free sets — map to faces). -/
  simpl : ∀ p q, toFun p = anti (toFun q) → p = anti q

namespace Z2Map

/-- The identity `ℤ₂`-map `Sⁿ → Sⁿ`. -/
def id (n : ℕ) : Z2Map n n where
  toFun := _root_.id
  equiv := by intro p; rfl
  simpl := by intro p q h; simpa using h

/-- Composition of `ℤ₂`-maps. -/
def comp {m n k : ℕ} (G : Z2Map n k) (F : Z2Map m n) : Z2Map m k where
  toFun := G.toFun ∘ F.toFun
  equiv := by
    intro p
    simp only [Function.comp_apply, F.equiv, G.equiv]
  simpl := by
    intro p q h
    exact F.simpl p q (G.simpl _ _ h)

/-- The equatorial inclusion `Sⁿ ↪ Sⁿ⁺¹` as a `ℤ₂`-map. -/
def incl (n : ℕ) : Z2Map n (n + 1) where
  toFun := fun p => (p.1.castSucc, p.2)
  equiv := by intro p; rfl
  simpl := by
    intro p q h
    obtain ⟨i, b⟩ := p; obtain ⟨j, c⟩ := q
    simp only [anti, Prod.mk.injEq] at h ⊢
    obtain ⟨h1, h2⟩ := h
    exact ⟨Fin.castSucc_injective _ h1, h2⟩

/-- The underlying vertex map of the suspension: the last coordinate (the two suspension
poles) is preserved, and every other coordinate is transported by `F`. -/
def suspFun {m n : ℕ} (F : Z2Map m n) : SVert (m + 1) → SVert (n + 1) :=
  fun p => Fin.lastCases (Fin.last (n + 1), p.2) (fun j => suspV (F.toFun (j, p.2))) p.1

@[simp] lemma suspFun_last {m n : ℕ} (F : Z2Map m n) (b : Bool) :
    F.suspFun (Fin.last (m + 1), b) = (Fin.last (n + 1), b) := by
  simp [suspFun]

@[simp] lemma suspFun_castSucc {m n : ℕ} (F : Z2Map m n) (j : Fin (m + 1)) (b : Bool) :
    F.suspFun (j.castSucc, b) = suspV (F.toFun (j, b)) := by
  simp [suspFun]

lemma suspFun_equiv {m n : ℕ} (F : Z2Map m n) (p : SVert (m + 1)) :
    F.suspFun (anti p) = anti (F.suspFun p) := by
  obtain ⟨i, b⟩ := p
  refine Fin.lastCases ?_ ?_ i
  · simp [anti]
  · intro j
    have hb : anti (j.castSucc, b) = (j.castSucc, !b) := rfl
    rw [hb, suspFun_castSucc, suspFun_castSucc, ← suspV_anti]
    congr 1
    exact F.equiv (j, b)

lemma suspFun_simpl {m n : ℕ} (F : Z2Map m n) (p q : SVert (m + 1)) :
    F.suspFun p = anti (F.suspFun q) → p = anti q := by
  obtain ⟨i, b⟩ := p; obtain ⟨j, c⟩ := q
  refine Fin.lastCases ?_ ?_ i <;> refine Fin.lastCases ?_ ?_ j
  · -- both last
    intro h
    rw [suspFun_last, suspFun_last] at h
    simp only [anti, Prod.mk.injEq] at h
    simp [anti, h.2]
  · -- i last, j castSucc
    intro j' h
    exfalso
    rw [suspFun_last, suspFun_castSucc] at h
    have hc := congrArg Prod.fst h
    simp only [anti, suspV] at hc
    exact absurd hc.symm (Fin.castSucc_lt_last _).ne
  · -- i castSucc, j last
    intro i' h
    exfalso
    rw [suspFun_last, suspFun_castSucc] at h
    have hc := congrArg Prod.fst h
    simp only [anti, suspV] at hc
    exact absurd hc (Fin.castSucc_lt_last _).ne
  · -- both castSucc
    intro j' i' h
    rw [suspFun_castSucc, suspFun_castSucc] at h
    have hF : F.toFun (i', b) = anti (F.toFun (j', c)) := by
      have h' := h
      simp only [suspV, anti, Prod.mk.injEq] at h'
      exact Prod.ext (Fin.castSucc_injective _ h'.1) h'.2
    have hpq := F.simpl (i', b) (j', c) hF
    simp only [anti, Prod.mk.injEq] at hpq
    rcases hpq with ⟨rfl, hb⟩
    simp [anti, hb]

/-- **Suspension of a `ℤ₂`-map.** A `ℤ₂`-map `Sᵐ → Sⁿ` suspends to a `ℤ₂`-map
`Sᵐ⁺¹ → Sⁿ⁺¹`: the last coordinate (the two suspension poles) is preserved, and every other
coordinate is transported by `F`. -/
def susp {m n : ℕ} (F : Z2Map m n) : Z2Map (m + 1) (n + 1) where
  toFun := F.suspFun
  equiv := F.suspFun_equiv
  simpl := F.suspFun_simpl

end Z2Map

/-! ## The constructive lower bound and the suspension increment -/




/-! ## Decidable reformulation via positive-vertex data -/

/-- A `ℤ₂`-equivariant vertex map is determined by the images of the *positive* vertices
`(i, true)`.  `induced g` reconstructs the full map from that data `g : Fin (m+1) → Sⁿ`. -/
def induced {m n : ℕ} (g : Fin (m + 1) → SVert n) : SVert m → SVert n :=
  fun p => if p.2 then g p.1 else anti (g p.1)



/-! ## Sharpness at the base: finite Borsuk–Ulam instances -/




end Z2CoindexSuspension


