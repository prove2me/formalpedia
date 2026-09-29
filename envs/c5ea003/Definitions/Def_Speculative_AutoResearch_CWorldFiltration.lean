-- Prove2me | Definitions.Def_Speculative_AutoResearch_CWorldFiltration
-- name    : Speculative_AutoResearch_CWorldFiltration
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:26:48.644269+00:00
-- url     : https://prove2.me/theorems/88bcf165-c42e-4c6c-a350-569eaf13d08f
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_CWorldFiltration
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.CWorldFiltration`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/CWorldFiltration.lean by skeleton subtraction
import Mathlib
/-
# Clock-and-Switch Worlds: a Filtration / Representation Theorem

## What this file does

A **clock-and-switch world** `CWorld A B` is a pair consisting of a *clock reading*
`clock : A` and a *switch configuration* `switch : B → Bool`.  Accessibility is the
product order: the clock may only advance, and a switch that has been flipped on can
never be flipped off again.  This is the canonical "monotone resource" frame:
`CWorld (Fin n) (Fin m)` is the product of an `n`-chain with an `m`-dimensional
Boolean cube.

The mission was to prove the **filtration lemma**: every finite rooted directed
preorder is a bounded (`p`-)morphic image of some `CWorld (Fin n) (Fin m)`, extending
the two special cases `forgetSwitches` (project a world to its clock) and `cardChain`
(count the switches that are on).

The honest answer, established here, is a **sharp characterisation** rather than the
literal statement, and both halves are nontrivial:

* `antisymm_of_representable` (adversarial finding).  A bounded morphic image of a
  *finite partial order* is again antisymmetric.  Since every `CWorld (Fin n) (Fin m)`
  is a finite partial order, a finite preorder with a genuine two-element cluster is
  **never** such an image.  So the literal statement "every finite rooted directed
  *preorder*" is false, and the correct hypothesis is "rooted directed *poset*".
  The proof is not formal: it picks a maximal element of the (finite) preimage of the
  putative cluster and pushes it up with the back condition.

* `representable_of_rooted_directed` (main theorem).  Conversely, **every** finite
  rooted directed partial order `P` is a surjective bounded morphic image of
  `CWorld (Fin 1) (Fin (card P))`.  The morphism is the *greedy climb* `walk`: fix a
  linear extension `t 0, t 1, …` of `P` (Szpilrajn), start at the root, and read the
  switches left to right; when switch `i` is on, jump to `t i` if the current point
  still lies below `t i`, and otherwise jump to the top.  The "otherwise jump to the
  top" clause is exactly what makes the map monotone — the naive greedy walk without
  it is *not* monotone (see the Lab Notes below) — and the linear-extension property
  is exactly what makes it *open* (the back condition).

Combining the two halves gives `representable_iff`: for a finite preorder,

    representable by a clock-and-switch world  ↔  rooted ∧ directed ∧ antisymmetric.

The antisymmetry clause is removed again in `Combinatorics.CWorldClusterTolerant`, by
adjoining to the source an *indiscrete* phase coordinate; there the literal preorder
statement becomes true, and the number of phases needed is exactly the largest cluster
size of the target.

## Lab Notes (experimental data behind the theorems)

Exhaustive machine search over all labelled bounded posets (`= rooted + directed +
finite`) confirmed representability before the proof was attempted:

* all 36 bounded posets on 4 labelled points: representable, cube dimension `m ≤ 3`;
* all 380 bounded posets on 5 labelled points: representable, `m ≤ 4`;
* the 6-point "bowtie" `0 < a,b < c,d < 1` (not a lattice): representable with `m = 3`
  by `000↦0, 001↦c, 010↦a, 100↦b, 011↦c, 101↦c, 110↦d, 111↦1`.

Minimal cube dimensions found: 3-chain `m = 2`, 4-chain `m = 3`, 5-chain `m = 4`,
diamond `m = 2`, so `m` must be at least the height of `P` and at least `log₂ |P|`;
the theorem below spends `m = |P|`, which is not claimed to be optimal.

Counterexample hunt for monotonicity of the naive greedy walk (no "jump to the top"):
on the diamond `0 < a,b < 1` with linear extension `0,a,b,1`, switches `{b}` walk to
`b` while switches `{a,b}` walk to `a`, and `b ≰ a`.  This is the failure the `tp`
branch of `walk` repairs.

Every theorem below is proved with no `sorry` and no `native_decide`.
-/


namespace CWorldFiltration

open Function

attribute [local instance] Classical.propDecidable

/-! ## Part A — Clock-and-switch worlds -/

/-- A **clock-and-switch world**: a clock reading in `A` together with a configuration
of switches indexed by `B`. -/
structure CWorld (A B : Type*) where
  /-- the clock reading -/
  clock : A
  /-- which switches are on -/
  switch : B → Bool

namespace CWorld

variable {A B : Type*}

/-- Accessibility: the clock advances and switches may only be turned on. -/
instance instPreorder [Preorder A] : Preorder (CWorld A B) where
  le w v := w.clock ≤ v.clock ∧ ∀ b, w.switch b = true → v.switch b = true
  le_refl _ := ⟨le_rfl, fun _ h => h⟩
  le_trans _ _ _ h₁ h₂ := ⟨le_trans h₁.1 h₂.1, fun b hb => h₂.2 b (h₁.2 b hb)⟩


instance instPartialOrder [PartialOrder A] : PartialOrder (CWorld A B) where
  le_antisymm w v h₁ h₂ := by
    obtain ⟨w1, w2⟩ := w
    obtain ⟨v1, v2⟩ := v
    have hc : w1 = v1 := le_antisymm h₁.1 h₂.1
    subst hc
    have hs : w2 = v2 := by
      funext b
      cases hw : w2 b <;> cases hv : v2 b
      · rfl
      · have := h₂.2 b (by simp [hv]); simp [hw] at this
      · have := h₁.2 b (by simp [hw]); simp [hv] at this
      · rfl
    simp [hs]



/-- `CWorld A B` is the product `A × (B → Bool)`. -/
def equivProd : CWorld A B ≃ A × (B → Bool) where
  toFun w := (w.clock, w.switch)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance instFintype [Fintype A] [Fintype B] [DecidableEq B] : Fintype (CWorld A B) :=
  Fintype.ofEquiv _ equivProd.symm


end CWorld

/-! ## Part B — Bounded morphisms (p-morphisms) -/

/-- A **bounded morphism** (p-morphism) of preorders: monotone (`forth`) and open
(`back`). -/
structure BddMorphism (X Y : Type*) [Preorder X] [Preorder Y] where
  /-- the underlying map -/
  toFun : X → Y
  /-- forth condition: the map is monotone -/
  forth : ∀ ⦃x y : X⦄, x ≤ y → toFun x ≤ toFun y
  /-- back condition: every point above the image of `x` is the image of a point above `x` -/
  back : ∀ (x : X) (q : Y), toFun x ≤ q → ∃ y, x ≤ y ∧ toFun y = q

namespace BddMorphism

variable {X Y Z : Type*} [Preorder X] [Preorder Y] [Preorder Z]

/-- Bounded morphisms compose. -/
def comp (g : BddMorphism Y Z) (f : BddMorphism X Y) : BddMorphism X Z where
  toFun := g.toFun ∘ f.toFun
  forth _ _ h := g.forth (f.forth h)
  back x q h := by
    obtain ⟨y, hy, rfl⟩ := g.back (f.toFun x) q h
    obtain ⟨z, hz, rfl⟩ := f.back x y hy
    exact ⟨z, hz, rfl⟩





end BddMorphism

/-! ## Part C — The two catalogued special cases, and clock padding -/

/-- `forgetSwitches`: reading only the clock is a surjective bounded morphism onto the
clock chain.  (Back condition: to realise a later clock reading, keep the switches —
or turn them all on.) -/
def forgetSwitches (A B : Type*) [Preorder A] : BddMorphism (CWorld A B) A where
  toFun w := w.clock
  forth _ _ h := h.1
  back w a h := ⟨⟨a, w.switch⟩, ⟨h, fun _ hb => hb⟩, rfl⟩


/-- The number of switches that are currently on. -/
def switchCount {m : ℕ} (w : CWorld (Fin 1) (Fin m)) : ℕ :=
  (Finset.univ.filter fun b => w.switch b = true).card

theorem switchCount_lt {m : ℕ} (w : CWorld (Fin 1) (Fin m)) : switchCount w < m + 1 := by
  have h := Finset.card_filter_le (Finset.univ : Finset (Fin m)) (fun b => w.switch b = true)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  simpa [switchCount] using Nat.lt_succ_of_le h

theorem switchCount_indicator {m : ℕ} (c : Fin 1) (u : Finset (Fin m)) :
    switchCount ⟨c, fun b => decide (b ∈ u)⟩ = u.card := by
  have hset : (Finset.univ.filter fun b : Fin m => (decide (b ∈ u)) = true) = u := by
    ext b; simp
  simp only [switchCount, hset]

/-- `cardChain`: counting the switches that are on is a surjective bounded morphism from
the `m`-cube onto the chain `Fin (m+1)`.  (Back condition: any target count can be
realised by enlarging the set of switches that are on.) -/
def cardChain (m : ℕ) : BddMorphism (CWorld (Fin 1) (Fin m)) (Fin (m + 1)) where
  toFun w := ⟨switchCount w, switchCount_lt w⟩
  forth w v h := by
    refine Fin.mk_le_mk.mpr (Finset.card_le_card ?_)
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    exact h.2 b hb
  back w j h := by
    have hle : switchCount w ≤ (j : ℕ) := h
    have hj : (j : ℕ) ≤ (Finset.univ : Finset (Fin m)).card := by
      have := j.isLt
      simp only [Finset.card_univ, Fintype.card_fin]
      omega
    obtain ⟨u, hu₁, -, hu₃⟩ :=
      Finset.exists_subsuperset_card_eq
        (Finset.subset_univ (Finset.univ.filter fun b => w.switch b = true)) hle hj
    refine ⟨⟨w.clock, fun b => decide (b ∈ u)⟩, ⟨le_rfl, ?_⟩, Fin.ext ?_⟩
    · intro b hb
      have : b ∈ u := hu₁ (by simpa using hb)
      simpa using this
    · show switchCount _ = (j : ℕ)
      rw [switchCount_indicator, hu₃]


/-- Padding the clock: collapsing a long clock to a trivial one is a surjective bounded
morphism, so the switch dimension is what matters and the clock length may be chosen
freely. -/
def clockPad (n m : ℕ) : BddMorphism (CWorld (Fin (n + 1)) (Fin m)) (CWorld (Fin 1) (Fin m)) where
  toFun w := ⟨0, w.switch⟩
  forth _ _ h := ⟨le_rfl, h.2⟩
  back w v h := ⟨⟨w.clock, v.switch⟩, ⟨le_rfl, h.2⟩, by
    obtain ⟨v1, v2⟩ := v
    simp only [CWorld.mk.injEq, and_true]
    exact Subsingleton.elim _ _⟩


/-! ## Part D — The greedy climb and the representation theorem -/



/-- The **greedy climb**.  Reading the switches `s 0, s 1, …` from left to right,
starting at the root `r`: when switch `i` is on, jump to `t i` if the current point is
still below `t i`, and jump to the top `tp` otherwise. -/
noncomputable def walk {P : Type*} [PartialOrder P] (t : ℕ → P) (r tp : P) (s : ℕ → Bool) :
    ℕ → P
  | 0 => r
  | i + 1 => if s i = true then (if walk t r tp s i ≤ t i then t i else tp)
             else walk t r tp s i

namespace walk

variable {P : Type*} [PartialOrder P] {t : ℕ → P} {r tp : P}







end walk

/-- `P` is **representable** if it is a surjective bounded morphic image of some
clock-and-switch world on finitely many clock ticks and finitely many switches. -/
def Representable (P : Type*) [Preorder P] : Prop :=
  ∃ (n m : ℕ) (f : BddMorphism (CWorld (Fin n) (Fin m)) P), Surjective f.toFun



/-! ## Part E — The characterisation, and its consequences -/






/-- The two-element **cluster**: two distinct points, each accessible from the other.
It is finite, rooted and directed, but not antisymmetric. -/
def Cluster : Type := Bool

instance : Preorder Cluster where
  le _ _ := True
  le_refl _ := trivial
  le_trans _ _ _ _ _ := trivial

instance : Fintype Cluster := inferInstanceAs (Fintype Bool)

instance : Nonempty Cluster := inferInstanceAs (Nonempty Bool)




end CWorldFiltration


