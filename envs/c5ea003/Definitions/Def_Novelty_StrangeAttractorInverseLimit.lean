-- Prove2me | Definitions.Def_Novelty_StrangeAttractorInverseLimit
-- name    : Novelty_StrangeAttractorInverseLimit
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:41:53.230578+00:00
-- url     : https://prove2.me/theorems/7641f084-37a6-4cc3-9ae3-e21ff4b722fc
-- title:
--   Aether Catalog definitions — Novelty_StrangeAttractorInverseLimit
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.StrangeAttractorInverseLimit`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/StrangeAttractorInverseLimit.lean by skeleton subtraction
import Mathlib

/-!
# Strange attractors as algebraic objects, I: the inverse-limit theorem

This file deepens `Novelty.StrangeAttractorsAlgebraic`, where binary de Bruijn graphs were
used to build a Cantor-like inverse limit.  Here the construction is carried out for an
*arbitrary* finite directed graph, and the central conjecture of the research thread is
proved in full:

> the space of infinite orbits of a symbolic (graph) dynamical system **is** the inverse
> limit of the diagram of its finite path sets in the category of finite sets, the bonding
> maps being edge deletion.

A finite directed graph is encoded as a `Bool`-valued edge relation `E : V → V → Bool` on a
finite vertex type.  For each `n` the *finite* set `FinPath E n` of paths with `n` edges is
a `Fintype`, and `truncPath` deletes the last edge.  The main results are:

* `invLimitEquiv` : `PathSpace E ≃ InvLimit E`, the inverse-limit theorem;
* `invLimitEquiv_shift` / `shift_toInvLimit` : the shift is visible on the finite level;
* `truncPath_surjective` : with no dead ends the bonding maps are surjective, so the
  diagram is a genuine (non-degenerate) tower;
* `finPath_card_pos`: the finite approximants are nonempty when there are no dead ends;
* `ClosedWalk`, `PeriodicPoints`, `IsConjugate`: the vocabulary used downstream for the
  zeta function, the periodic-orbit count and conjugacy invariants.

The geometric Lorenz attractor is the inverse limit of its branched-manifold (template)
first-return graph; the theorems below are the algebraic skeleton of that statement, and
`Novelty.StrangeAttractorLorenzTemplate` instantiates them at the Lorenz template.
-/

namespace LorenzLimit

variable {V : Type*}

/-! ## Finite path sets and bonding maps -/

/-- A path with `n` edges in the directed graph with edge relation `E`. -/
def FinPath (E : V → V → Bool) (n : ℕ) : Type _ :=
  {w : Fin (n + 1) → V // ∀ i : Fin n, E (w i.castSucc) (w i.succ) = true}

instance instFintypeFinPath (E : V → V → Bool) (n : ℕ) [Fintype V] : Fintype (FinPath E n) := by
  unfold FinPath; infer_instance

instance instDecidableEqFinPath (E : V → V → Bool) (n : ℕ) [DecidableEq V] :
    DecidableEq (FinPath E n) := by
  unfold FinPath; infer_instance


/-- The bonding map of the tower: delete the last edge of a path. -/
def truncPath (E : V → V → Bool) (n : ℕ) (w : FinPath E (n + 1)) : FinPath E n :=
  ⟨fun i => w.1 i.castSucc, fun i => by
    have := w.2 i.castSucc
    simpa [Fin.castSucc, Fin.succ] using this⟩

/-- The set of infinite forward orbits (infinite paths) of the graph. -/
def pathSet (E : V → V → Bool) : Set (ℕ → V) := {x | ∀ n, E (x n) (x (n + 1)) = true}

/-- The space of infinite forward orbits of the graph. -/
def PathSpace (E : V → V → Bool) : Type _ := ↥(pathSet E)

/-- The inverse limit of the tower of finite path sets. -/
def InvLimit (E : V → V → Bool) : Type _ :=
  {f : ∀ n, FinPath E n // ∀ n, truncPath E n (f (n + 1)) = f n}

variable {E : V → V → Bool}


theorem PathSpace.edge (x : PathSpace E) (n : ℕ) : E (x.1 n) (x.1 (n + 1)) = true := x.2 n

/-! ## The inverse-limit theorem -/

/-- Coherence: a compatible thread in the tower is determined by the terminal vertices of
its members. -/
theorem invLimit_coherent (f : InvLimit E) :
    ∀ n (i : Fin (n + 1)), (f.1 n).1 i = (f.1 i.val).1 (Fin.last i.val) := by
  intro n
  induction n with
  | zero => intro i; fin_cases i; rfl
  | succ n ih =>
      intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · have h := f.2 n
        have h' : (truncPath E n (f.1 (n + 1))).1 j = (f.1 n).1 j := by rw [h]
        simp only [truncPath] at h'
        rw [h', ih j]
        rfl
      · rfl

/-- Restriction of an infinite path to its first `n` edges. -/
def toFinPath (x : PathSpace E) (n : ℕ) : FinPath E n :=
  ⟨fun i => x.1 i.val, fun i => x.2 i.val⟩

theorem truncPath_toFinPath (x : PathSpace E) (n : ℕ) :
    truncPath E n (toFinPath x (n + 1)) = toFinPath x n := rfl

/-- The compatible thread of finite restrictions of an infinite path. -/
def toInvLimit (x : PathSpace E) : InvLimit E :=
  ⟨toFinPath x, fun n => truncPath_toFinPath x n⟩

/-- The infinite path assembled from a compatible thread. -/
def ofInvLimit (f : InvLimit E) : PathSpace E :=
  ⟨fun n => (f.1 n).1 (Fin.last n), by
    intro n
    have h := (f.1 (n + 1)).2 (Fin.last n)
    have h1 : (f.1 (n + 1)).1 (Fin.castSucc (Fin.last n)) = (f.1 n).1 (Fin.last n) :=
      invLimit_coherent f (n + 1) (Fin.castSucc (Fin.last n))
    have h2 : (Fin.last n).succ = Fin.last (n + 1) := rfl
    rw [h1, h2] at h
    exact h⟩

/-- **The inverse-limit theorem.**  The space of infinite orbits of a finite directed graph
is canonically isomorphic to the inverse limit of the diagram of its finite path sets, with
edge deletion as bonding maps. -/
def invLimitEquiv : PathSpace E ≃ InvLimit E where
  toFun := toInvLimit
  invFun := ofInvLimit
  left_inv _ := rfl
  right_inv f := by
    apply Subtype.ext
    funext n
    apply Subtype.ext
    funext i
    simp only [toInvLimit, toFinPath, ofInvLimit]
    exact (invLimit_coherent f n i).symm

/-! ## The shift -/

/-- The (one-sided) shift on infinite orbits: forget the initial vertex. -/
def shift (x : PathSpace E) : PathSpace E := ⟨fun n => x.1 (n + 1), fun n => x.2 (n + 1)⟩





/-! ## Non-degeneracy of the tower -/

/-- Every vertex has an outgoing edge. -/
def NoDeadEnds (E : V → V → Bool) : Prop := ∀ v : V, ∃ w, E v w = true

/-- Extend a finite path by one edge. -/
def extendPath (E : V → V → Bool) (n : ℕ) (w : FinPath E n) (v : V)
    (h : E (w.1 (Fin.last n)) v = true) : FinPath E (n + 1) :=
  ⟨Fin.snoc w.1 v, by
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · have h1 : (Fin.snoc w.1 v : Fin (n + 2) → V) (Fin.castSucc j).castSucc = w.1 j.castSucc :=
        Fin.snoc_castSucc (α := fun _ => V) v w.1 j.castSucc
      have h2 : (Fin.snoc w.1 v : Fin (n + 2) → V) (Fin.castSucc j).succ = w.1 j.succ := by
        rw [Fin.succ_castSucc]
        exact Fin.snoc_castSucc (α := fun _ => V) v w.1 j.succ
      rw [h1, h2]
      exact w.2 j
    · have h1 : (Fin.snoc w.1 v : Fin (n + 2) → V) (Fin.castSucc (Fin.last n)) = w.1 (Fin.last n) :=
        Fin.snoc_castSucc (α := fun _ => V) v w.1 (Fin.last n)
      have h2 : (Fin.snoc w.1 v : Fin (n + 2) → V) (Fin.last n).succ = v := by
        rw [Fin.succ_last]; exact Fin.snoc_last (α := fun _ => V) v w.1
      rw [h1, h2]
      exact h⟩





/-- Every vertex has at least two outgoing edges: the branching condition responsible for
chaos (positive entropy) in the symbolic model. -/
def Branching (E : V → V → Bool) : Prop :=
  ∀ v : V, ∃ u u' : V, u ≠ u' ∧ E v u = true ∧ E v u' = true

theorem Branching.noDeadEnds (h : Branching E) : NoDeadEnds E := fun v =>
  let ⟨u, _, _, hu, _⟩ := h v; ⟨u, hu⟩

/-! ## Closed walks and periodic orbits -/

/-- A closed walk with `n` edges: a finite path returning to its starting vertex. -/
def ClosedWalk (E : V → V → Bool) (n : ℕ) : Type _ :=
  {w : FinPath E n // w.1 0 = w.1 (Fin.last n)}

instance instFintypeClosedWalk (E : V → V → Bool) (n : ℕ) [Fintype V] [DecidableEq V] :
    Fintype (ClosedWalk E n) := by
  unfold ClosedWalk; infer_instance

/-- The set of points of period (dividing) `n` for the shift. -/
def PeriodicPoints (E : V → V → Bool) (n : ℕ) : Type _ :=
  {x : PathSpace E // shift^[n] x = x}

/-- Topological conjugacy of two symbolic systems: a bijection of orbit spaces commuting
with the shift. -/
def IsConjugate {W : Type*} (E : V → V → Bool) (F : W → W → Bool) : Prop :=
  ∃ φ : PathSpace E ≃ PathSpace F, ∀ x, φ (shift x) = shift (φ x)




/-! ## Nonemptiness of the inverse limit -/

/-- The orbit produced by always following a chosen outgoing edge. -/
noncomputable def deadEndFreeSeq (h : NoDeadEnds E) (v₀ : V) : ℕ → V
  | 0 => v₀
  | n + 1 => (h (deadEndFreeSeq h v₀ n)).choose


end LorenzLimit


