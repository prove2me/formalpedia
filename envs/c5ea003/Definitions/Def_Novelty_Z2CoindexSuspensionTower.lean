-- Prove2me | Definitions.Def_Novelty_Z2CoindexSuspensionTower
-- name    : Novelty_Z2CoindexSuspensionTower
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:54:00.968871+00:00
-- url     : https://prove2.me/theorems/29ff1014-ef97-4933-93dd-2473f8c82196
-- title:
--   Aether Catalog definitions — Novelty_Z2CoindexSuspensionTower
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.Z2CoindexSuspensionTower`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/Z2CoindexSuspensionTower.lean by skeleton subtraction
import Mathlib
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

namespace Z2SuspensionTower

open Function

/-! ## Vertices of the combinatorial sphere and the antipodal action -/

/-- Vertices of the `n`-dimensional combinatorial sphere `Sⁿ`: `(i, b)` encodes `±eᵢ`. -/
abbrev SVert (n : ℕ) := Fin (n + 1) × Bool

/-- The antipodal map, the free `ℤ₂`-action `±eᵢ ↦ ∓eᵢ`. -/
def anti {n : ℕ} (p : SVert n) : SVert n := (p.1, !p.2)



/-! ## ℤ₂-maps of combinatorial spheres -/

/-- A `ℤ₂`-map of combinatorial spheres `Sᵐ → Sⁿ`: a simplicial map of the cross-polytope boundary
complexes that commutes with the antipodal action. -/
structure Z2Map (m n : ℕ) where
  /-- The underlying vertex map. -/
  toFun : SVert m → SVert n
  /-- Equivariance with respect to the antipodal `ℤ₂`-action. -/
  equiv : ∀ p, toFun (anti p) = anti (toFun p)
  /-- Simpliciality: two vertices land on an antipodal pair only if they were antipodal. -/
  simpl : ∀ p q, toFun p = anti (toFun q) → p = anti q

namespace Z2Map


/-! ### The suspension functor on maps -/

/-- The suspension of a vertex: reuse the same index in the enlarged sphere `Sⁿ⁺¹`. -/
def suspV {n : ℕ} (p : SVert n) : SVert (n + 1) := (p.1.castSucc, p.2)

lemma suspV_anti {n : ℕ} (p : SVert n) : suspV (anti p) = anti (suspV p) := by
  simp [suspV, anti]

/-- The underlying vertex map of the suspension. -/
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
  · intro h
    rw [suspFun_last, suspFun_last] at h
    simp only [anti, Prod.mk.injEq] at h
    simp [anti, h.2]
  · intro j' h
    exfalso
    rw [suspFun_last, suspFun_castSucc] at h
    have hc := congrArg Prod.fst h
    simp only [anti, suspV] at hc
    exact absurd hc.symm (Fin.castSucc_lt_last _).ne
  · intro i' h
    exfalso
    rw [suspFun_last, suspFun_castSucc] at h
    have hc := congrArg Prod.fst h
    simp only [anti, suspV] at hc
    exact absurd hc (Fin.castSucc_lt_last _).ne
  · intro j' i' h
    rw [suspFun_castSucc, suspFun_castSucc] at h
    have hF : F.toFun (i', b) = anti (F.toFun (j', c)) := by
      have h' := h
      simp only [suspV, anti, Prod.mk.injEq] at h'
      exact Prod.ext (Fin.castSucc_injective _ h'.1) h'.2
    have hpq := F.simpl (i', b) (j', c) hF
    simp only [anti, Prod.mk.injEq] at hpq
    rcases hpq with ⟨rfl, hb⟩
    simp [anti, hb]

/-- **Suspension of a `ℤ₂`-map** `Sᵐ → Sⁿ` to a `ℤ₂`-map `Sᵐ⁺¹ → Sⁿ⁺¹`. -/
def susp {m n : ℕ} (F : Z2Map m n) : Z2Map (m + 1) (n + 1) where
  toFun := F.suspFun
  equiv := F.suspFun_equiv
  simpl := F.suspFun_simpl

end Z2Map

/-! ## Decidable / finite reformulation via positive-vertex data -/

/-- An equivariant vertex map is determined by the images of the positive vertices `(i, true)`.
`induced g` reconstructs the full map from that data `g : Fin (m+1) → SVert n`. -/
def induced {m n : ℕ} (g : Fin (m + 1) → SVert n) : SVert m → SVert n :=
  fun p => if p.2 then g p.1 else anti (g p.1)

lemma induced_equiv {m n : ℕ} (g : Fin (m + 1) → SVert n) (p : SVert m) :
    induced g (anti p) = anti (induced g p) := by
  obtain ⟨i, b⟩ := p; cases b <;> simp [induced, anti]


/-! ## Simpliciality of the induced map is injectivity of the coordinate map -/

/-- The coordinate (index) component of positive-vertex data. -/
def coordMap {m n : ℕ} (g : Fin (m + 1) → SVert n) : Fin (m + 1) → Fin (n + 1) :=
  fun i => (g i).1

/-- **The combinatorial heart.** The map induced by positive-vertex data `g` is simplicial (no two
non-antipodal vertices map to an antipodal pair) **iff** its coordinate map `i ↦ (g i).1` is
injective.  A simplicial antipodal map of cross-polytopes is exactly an injection of coordinate axes
with arbitrary signs. -/
theorem induced_simplicial_iff_injective {m n : ℕ} (g : Fin (m + 1) → SVert n) :
    (∀ p q, induced g p = anti (induced g q) → p = anti q) ↔ Function.Injective (coordMap g) := by
  constructor
  · intro H i j hij
    by_cases hb : (g i).2 = (g j).2
    · have hgeq : g i = g j := Prod.ext hij hb
      exact congrArg Prod.fst (H (i, true) (j, false) (by simp [induced, anti, hgeq]))
    · have hgeq : g i = ((g j).1, !(g j).2) := by
        refine Prod.ext hij ?_
        revert hb; cases (g i).2 <;> cases (g j).2 <;> simp
      exact congrArg Prod.fst (H (i, true) (j, true) (by simp [induced, anti, hgeq]))
  · intro hinj p q h
    obtain ⟨i, b⟩ := p; obtain ⟨j, c⟩ := q
    have hfst : coordMap g i = coordMap g j := by
      have hh := congrArg Prod.fst h
      simp only [induced, anti, coordMap] at hh ⊢
      cases b <;> cases c <;> simpa using hh
    have hij : i = j := hinj hfst
    subst hij
    have hsnd := congrArg Prod.snd h
    simp only [induced, anti] at hsnd
    simp only [anti]
    cases b <;> cases c <;> simp_all

/-! ## The exact coindex criterion -/



/-! ## The exact coindex -/

/-- The `ℤ₂`-coindex of the combinatorial sphere `Sⁿ`: the supremum of source dimensions `m`
admitting a `ℤ₂`-map `Sᵐ → Sⁿ`. -/
noncomputable def coind (n : ℕ) : ℕ := sSup {m | Nonempty (Z2Map m n)}


/-! ## The suspension tower -/

/-- The `k`-fold suspension of a `ℤ₂`-map: iterate `Z2Map.susp` `k` times. -/
def Z2Map.suspIter {m n : ℕ} : (k : ℕ) → Z2Map m n → Z2Map (m + k) (n + k)
  | 0, F => F
  | k + 1, F => (F.suspIter k).susp





end Z2SuspensionTower


