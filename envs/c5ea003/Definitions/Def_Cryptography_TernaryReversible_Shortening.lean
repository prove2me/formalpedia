-- Prove2me | Definitions.Def_Cryptography_TernaryReversible_Shortening
-- name    : Cryptography_TernaryReversible_Shortening
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T18:14:06.998221+00:00
-- url     : https://prove2.me/theorems/e3ff71ae-692b-483c-b2d0-ae2251a42cf5
-- title:
--   Aether Catalog definitions — Cryptography_TernaryReversible_Shortening
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.TernaryReversible.Shortening`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/TernaryReversible/Shortening.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core
import Definitions.Def_Cryptography_TernaryReversible_General
import Theorems.Thm_Cryptography_TernaryReversible_bijective_iff_injective_globalMapA

/-!
# A finite test for cycle-bijectivity: the splicing bound

Cycle-bijectivity quantifies over *all* cycle lengths.  This file proves that the
quantifier is in fact finite: for an alphabet with `q` letters it suffices to test the
cycle lengths `1, 2, …, q⁴`.

The proof is a splicing (pigeonhole) argument on the **pair graph**.  A failure of
injectivity on the cycle `ℤ/n` is the same thing as a pair of `n`-periodic sequences
`S, T : ℕ → A` that are *locally compatible*,

`g (S k) (S (k+1)) (S (k+2)) = g (T k) (T (k+1)) (T (k+2))` for all `k`,

and differ somewhere (`HasCollision`).  The `q⁴` states `(S k, S (k+1), T k, T (k+1))`
force a repetition at two positions `i < j ≤ q⁴` whenever `n > q⁴`, and at such a
repetition the cyclic word can be cut in two ways:

* **keep the loop** `[i, j)`, giving period `j - i`;
* **delete the loop**, giving period `n - (j - i)`.

Both are legitimate because the two boundary states agree, and whichever half still
contains a position where `S` and `T` differ is a *strictly shorter* collision; induction
on the length finishes the proof.  The bookkeeping is packaged in `periodic_loop`: for any
sequence `U` with `U a = U (a+p)` and `U (a+1) = U (a+p+1)`, the wrapped sequence
`k ↦ U (a + k % p)` is `p`-periodic and its one- and two-step shifts are the shifts of `U`,
so a window-three local condition survives the splice.

## Main results

* `hasCollision_iff_not_injective` — collisions of period `p` are exactly the failures of
  injectivity on the cycle of length `p`;
* `periodic_loop`, `collision_of_loop` — the splicing lemmas;
* `exists_small_collision` — every collision shortens to one of period at most `q⁴`;
* `cycleBijectiveA_iff_upTo` — **cycle-bijectivity is decided by the cycle lengths `≤ q⁴`**;
* `decidableCycleBijectiveA`, `decidableCycleBijective` — consequently cycle-bijectivity is
  a decidable property of the local rule;
* `cycleBijectiveA_iff_single_length` — even a *single* cycle length, `(q⁴)!`, decides it;
* `cycleBijective_iff_upTo_81` — the ternary case: the lengths `1, …, 81` suffice.
-/

namespace Cryptography
namespace TernaryReversible

variable {A : Type}

/-! ## Collisions -/

/-- Local compatibility of two `ℕ`-indexed configurations under the rule `g`. -/
def LocEq (g : A → A → A → A) (S T : ℕ → A) : Prop :=
  ∀ k : ℕ, g (S k) (S (k + 1)) (S (k + 2)) = g (T k) (T (k + 1)) (T (k + 2))

/-- A *collision of period `p`*: two `p`-periodic, locally compatible sequences that differ
somewhere.  This is the unrolled form of a failure of injectivity on the cycle `ℤ/p`. -/
def HasCollision (g : A → A → A → A) (p : ℕ) : Prop :=
  ∃ S T : ℕ → A, Function.Periodic S p ∧ Function.Periodic T p ∧ LocEq g S T ∧ ∃ k, S k ≠ T k

/-- Transport of a periodic sequence along a congruence of indices. -/
theorem periodic_val_congr {U : ℕ → A} {p : ℕ} [NeZero p] (hU : Function.Periodic U p)
    {x : ZMod p} {m : ℕ} (h : (m : ZMod p) = x) : U x.val = U m := by
  have hcast : ((x.val : ℕ) : ZMod p) = ((m : ℕ) : ZMod p) := by
    rw [ZMod.natCast_rightInverse x, h]
  have hmod : x.val % p = m % p := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hcast
  rw [← hU.map_mod_nat x.val, ← hU.map_mod_nat m, hmod]

/-- A failure of injectivity on the cycle of length `p` unrolls to a collision. -/
theorem hasCollision_of_not_injective {g : A → A → A → A} {p : ℕ} (hp : 0 < p)
    (h : ¬ Function.Injective (globalMapA (n := p) g)) : HasCollision g p := by
  haveI : NeZero p := ⟨hp.ne'⟩
  rw [Function.not_injective_iff] at h
  obtain ⟨s, t, hst, hne⟩ := h
  refine ⟨fun k => s (k : ZMod p), fun k => t (k : ZMod p), ?_, ?_, ?_, ?_⟩
  · intro x
    simp
  · intro x
    simp
  · intro k
    have hk := congrFun hst ((k : ZMod p) + 1)
    have hL : globalMapA (n := p) g s ((k : ZMod p) + 1)
        = g (s (k : ZMod p)) (s ((k + 1 : ℕ) : ZMod p)) (s ((k + 2 : ℕ) : ZMod p)) := by
      simp only [globalMapA, add_sub_cancel_right]
      push_cast
      ring_nf
    have hR : globalMapA (n := p) g t ((k : ZMod p) + 1)
        = g (t (k : ZMod p)) (t ((k + 1 : ℕ) : ZMod p)) (t ((k + 2 : ℕ) : ZMod p)) := by
      simp only [globalMapA, add_sub_cancel_right]
      push_cast
      ring_nf
    rw [hL, hR] at hk
    exact hk
  · by_contra hall
    push_neg at hall
    refine hne (funext fun i => ?_)
    have := hall i.val
    rwa [ZMod.natCast_rightInverse i] at this

/-- Conversely, a collision of period `p` breaks injectivity on the cycle of length `p`. -/
theorem not_injective_of_hasCollision {g : A → A → A → A} {p : ℕ} (hp : 0 < p)
    (h : HasCollision g p) : ¬ Function.Injective (globalMapA (n := p) g) := by
  haveI : NeZero p := ⟨hp.ne'⟩
  obtain ⟨S, T, hS, hT, hloc, k, hk⟩ := h
  intro hinj
  apply hk
  have key : globalMapA (n := p) g (fun i => S i.val)
      = globalMapA (n := p) g (fun i => T i.val) := by
    funext i
    have hm1 : ∀ (U : ℕ → A), Function.Periodic U p → U (i - 1).val = U (i.val + p - 1) := by
      intro U hU
      refine periodic_val_congr hU ?_
      have hp1 : ((p - 1 : ℕ) : ZMod p) = (p : ZMod p) - 1 := by
        rw [Nat.cast_sub hp]
        simp
      have hsplit : i.val + p - 1 = i.val + (p - 1) := by omega
      rw [hsplit]
      push_cast [hp1]
      rw [ZMod.natCast_rightInverse i, ZMod.natCast_self]
      ring
    have hm0 : ∀ (U : ℕ → A), Function.Periodic U p → U i.val = U (i.val + p) := by
      intro U hU
      exact (hU i.val).symm
    have hm2 : ∀ (U : ℕ → A), Function.Periodic U p → U (i + 1).val = U (i.val + p + 1) := by
      intro U hU
      refine periodic_val_congr hU ?_
      push_cast
      rw [ZMod.natCast_rightInverse i, ZMod.natCast_self]
      ring
    have e1 : i.val + p - 1 + 1 = i.val + p := by omega
    have e2 : i.val + p - 1 + 2 = i.val + p + 1 := by omega
    show g (S (i - 1).val) (S i.val) (S (i + 1).val)
        = g (T (i - 1).val) (T i.val) (T (i + 1).val)
    rw [hm1 S hS, hm0 S hS, hm2 S hS, hm1 T hT, hm0 T hT, hm2 T hT]
    have hl := hloc (i.val + p - 1)
    rwa [e1, e2] at hl
  have heq := congrFun (hinj key) (k : ZMod p)
  have hSk : S ((k : ZMod p)).val = S k := periodic_val_congr hS rfl
  have hTk : T ((k : ZMod p)).val = T k := periodic_val_congr hT rfl
  rw [hSk, hTk] at heq
  exact heq


/-! ## The splicing lemmas -/

/-- **Splicing.** If a sequence `U` returns to the same *pair* of consecutive values after
`p` steps, then wrapping it around the window `[a, a+p)` produces a `p`-periodic sequence
whose one- and two-step shifts are still the shifts of `U`.  Local conditions of window
three therefore survive the splice. -/
theorem periodic_loop {U : ℕ → A} {a p : ℕ} (hp : 0 < p)
    (h0 : U a = U (a + p)) (h1 : U (a + 1) = U (a + p + 1)) :
    Function.Periodic (fun k => U (a + k % p)) p ∧
      (∀ k, U (a + (k + 1) % p) = U (a + k % p + 1)) ∧
      (∀ k, U (a + (k + 2) % p) = U (a + k % p + 2)) := by
  refine ⟨fun k => by simp [Nat.add_mod_right], ?_, ?_⟩
  · intro k
    have hlt : k % p < p := Nat.mod_lt _ hp
    have hmod : (k + 1) % p = (k % p + 1) % p := ((Nat.mod_modEq k p).add_right 1).symm
    rcases Nat.lt_or_ge (k % p + 1) p with hcase | hcase
    · rw [hmod, Nat.mod_eq_of_lt hcase, ← Nat.add_assoc]
    · have heq : k % p + 1 = p := by omega
      rw [hmod, heq, Nat.mod_self]
      have hidx : a + k % p + 1 = a + p := by omega
      rw [hidx, ← h0, Nat.add_zero]
  · intro k
    have hlt : k % p < p := Nat.mod_lt _ hp
    have hmod : (k + 2) % p = (k % p + 2) % p := ((Nat.mod_modEq k p).add_right 2).symm
    rcases lt_trichotomy (k % p + 2) p with hcase | hcase | hcase
    · rw [hmod, Nat.mod_eq_of_lt hcase, ← Nat.add_assoc]
    · rw [hmod, hcase, Nat.mod_self]
      have hidx : a + k % p + 2 = a + p := by omega
      rw [hidx, ← h0, Nat.add_zero]
    · rcases Nat.lt_or_ge p 2 with hplt | hp2
      · have hp1' : p = 1 := by omega
        subst hp1'
        have e1 : U a = U (a + 1) := h0
        have e2 : U (a + 1) = U (a + 2) := by
          rw [show a + 2 = a + 1 + 1 by omega]
          exact h1
        simp only [Nat.mod_one, Nat.add_zero]
        exact e1.trans e2
      · have heq : k % p + 2 = p + 1 := by omega
        have hone : (k % p + 2) % p = 1 := by
          rw [heq, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
        rw [hmod, hone]
        have hidx : a + k % p + 2 = a + p + 1 := by omega
        rw [hidx, ← h1]

/-- Building a collision of period `p` out of a loop of the pair graph. -/
theorem collision_of_loop {g : A → A → A → A} {S T : ℕ → A} (hloc : LocEq g S T) {a p : ℕ}
    (hp : 0 < p) (h0S : S a = S (a + p)) (h1S : S (a + 1) = S (a + p + 1))
    (h0T : T a = T (a + p)) (h1T : T (a + 1) = T (a + p + 1))
    {w : ℕ} (hw : w < p) (hdiff : S (a + w) ≠ T (a + w)) : HasCollision g p := by
  obtain ⟨hperS, hsh1S, hsh2S⟩ := periodic_loop hp h0S h1S
  obtain ⟨hperT, hsh1T, hsh2T⟩ := periodic_loop hp h0T h1T
  refine ⟨fun k => S (a + k % p), fun k => T (a + k % p), hperS, hperT, ?_, w, ?_⟩
  · intro k
    show g (S (a + k % p)) (S (a + (k + 1) % p)) (S (a + (k + 2) % p))
        = g (T (a + k % p)) (T (a + (k + 1) % p)) (T (a + (k + 2) % p))
    rw [hsh1S k, hsh2S k, hsh1T k, hsh2T k]
    exact hloc (a + k % p)
  · show S (a + w % p) ≠ T (a + w % p)
    rwa [Nat.mod_eq_of_lt hw]

/-! ## Shortening -/

/-- One shortening step: a repeated pair-graph state at positions `i < j` inside a
collision of period `n` produces a collision of strictly smaller period — either the loop
`[i, j)` itself, or the cyclic word with that loop deleted, whichever still carries a
position where the two configurations differ. -/
theorem shorten_step {g : A → A → A → A} {n i j : ℕ} (hn : 0 < n)
    {S T : ℕ → A} (hS : Function.Periodic S n) (hT : Function.Periodic T n)
    (hloc : LocEq g S T) {u₀ : ℕ} (hu₀ : S u₀ ≠ T u₀) (hij : i < j) (hjn : j < n)
    (hfS : S i = S j) (hfS' : S (i + 1) = S (j + 1))
    (hfT : T i = T j) (hfT' : T (i + 1) = T (j + 1)) :
    ∃ m, 0 < m ∧ m < n ∧ HasCollision g m := by
  have hdj : i + (j - i) = j := by omega
  by_cases hcase : ∃ w, w < j - i ∧ S (i + w) ≠ T (i + w)
  · -- keep the loop `[i, j)`
    obtain ⟨w, hw, hdiff⟩ := hcase
    refine ⟨j - i, by omega, by omega, ?_⟩
    refine collision_of_loop hloc (a := i) (p := j - i) (by omega) ?_ ?_ ?_ ?_ hw hdiff
    · rw [hdj]; exact hfS
    · rw [show i + (j - i) + 1 = j + 1 by omega]; exact hfS'
    · rw [hdj]; exact hfT
    · rw [show i + (j - i) + 1 = j + 1 by omega]; exact hfT'
  · -- delete the loop: period `n - (j - i)`, window starting at `j`
    push_neg at hcase
    set p := n - (j - i) with hp
    have hp0 : 0 < p := by omega
    have hjp : j + p = i + n := by omega
    have h0S : S j = S (j + p) := by rw [hjp, hS i]; exact hfS.symm
    have h1S : S (j + 1) = S (j + p + 1) := by
      rw [show j + p + 1 = (i + 1) + n by omega, hS (i + 1)]
      exact hfS'.symm
    have h0T : T j = T (j + p) := by rw [hjp, hT i]; exact hfT.symm
    have h1T : T (j + 1) = T (j + p + 1) := by
      rw [show j + p + 1 = (i + 1) + n by omega, hT (i + 1)]
      exact hfT'.symm
    -- locate a differing position inside the surviving window `[j, j + p)`
    have hu : S (u₀ % n) ≠ T (u₀ % n) := by
      rwa [hS.map_mod_nat u₀, hT.map_mod_nat u₀]
    have hun : u₀ % n < n := Nat.mod_lt _ hn
    set u := u₀ % n with hudef
    by_cases hge : j ≤ u
    · refine ⟨p, hp0, by omega, ?_⟩
      refine collision_of_loop hloc (a := j) (p := p) hp0 h0S h1S h0T h1T (w := u - j)
        (by omega) ?_
      rw [show j + (u - j) = u by omega]
      exact hu
    · push_neg at hge
      have hui : u < i := by
        by_contra hcon
        push_neg at hcon
        have hcon2 := hcase (u - i) (by omega)
        rw [show i + (u - i) = u by omega] at hcon2
        exact hu hcon2
      refine ⟨p, hp0, by omega, ?_⟩
      refine collision_of_loop hloc (a := j) (p := p) hp0 h0S h1S h0T h1T (w := u + n - j)
        (by omega) ?_
      rw [show j + (u + n - j) = u + n by omega, hS u, hT u]
      exact hu

/-- **Shortening theorem.** Every collision can be spliced down to a collision of period at
most `q⁴`, where `q` is the number of letters. -/
theorem exists_small_collision [Fintype A] [DecidableEq A] {g : A → A → A → A} :
    ∀ n : ℕ, 0 < n → HasCollision g n →
      ∃ m, 0 < m ∧ m ≤ Fintype.card A ^ 4 ∧ HasCollision g m := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn hcol
    by_cases hsmall : n ≤ Fintype.card A ^ 4
    · exact ⟨n, hn, hsmall, hcol⟩
    push_neg at hsmall
    obtain ⟨S, T, hS, hT, hloc, u₀, hu₀⟩ := hcol
    set N := Fintype.card A ^ 4 with hNdef
    set f : ℕ → A × A × A × A := fun k => (S k, S (k + 1), T k, T (k + 1)) with hfdef
    have hcardprod : Fintype.card (A × A × A × A) = Fintype.card A ^ 4 := by
      simp [Fintype.card_prod]
      ring
    have hcard : (Finset.univ : Finset (A × A × A × A)).card < (Finset.range (N + 1)).card := by
      simp only [Finset.card_range, Finset.card_univ, hcardprod, ← hNdef]
      omega
    obtain ⟨i, hi, j, hj, hijne, hfij⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to hcard (fun x _ => Finset.mem_univ (f x))
    simp only [Finset.mem_range] at hi hj
    have main : ∀ i j : ℕ, i < j → j ≤ N → f i = f j → ∃ m, 0 < m ∧ m < n ∧ HasCollision g m := by
      intro i j hij hjN hfeq
      have h1 : S i = S j := congrArg (fun z => z.1) hfeq
      have h2 : S (i + 1) = S (j + 1) := congrArg (fun z => z.2.1) hfeq
      have h3 : T i = T j := congrArg (fun z => z.2.2.1) hfeq
      have h4 : T (i + 1) = T (j + 1) := congrArg (fun z => z.2.2.2) hfeq
      exact shorten_step hn hS hT hloc hu₀ hij (by omega) h1 h2 h3 h4
    have hsmaller : ∃ m, 0 < m ∧ m < n ∧ HasCollision g m := by
      rcases Nat.lt_or_ge i j with hlt | hge
      · exact main i j hlt (by omega) hfij
      · have hjlt : j < i := by omega
        exact main j i hjlt (by omega) hfij.symm
    obtain ⟨m, hm0, hmn, hmcol⟩ := hsmaller
    exact IH m hmn hm0 hmcol

/-! ## The finite test -/

/-- **Cycle-bijectivity is a finite test.** Over an alphabet with `q` letters, a radius-one
rule is bijective on every nonempty finite cycle as soon as its global map is injective on
the cycles of length `1, 2, …, q⁴`. -/
theorem cycleBijectiveA_iff_upTo [Fintype A] [DecidableEq A] (g : A → A → A → A) :
    CycleBijectiveA g ↔
      ∀ m : ℕ, 0 < m → m ≤ Fintype.card A ^ 4 → Function.Injective (globalMapA (n := m) g) := by
  constructor
  · intro hg m hm _
    exact (hg m hm).1
  · intro h n hn
    rw [bijective_iff_injective_globalMapA g hn]
    by_contra hbad
    obtain ⟨m, hm0, hmle, hmcol⟩ :=
      exists_small_collision n hn (hasCollision_of_not_injective hn hbad)
    exact not_injective_of_hasCollision hm0 hmcol (h m hm0 hmle)

/-- The same finite test, indexed so that every tested length is manifestly positive.  This
is the form that carries a decidability instance. -/
theorem cycleBijectiveA_iff_upTo' [Fintype A] [DecidableEq A] (g : A → A → A → A) :
    CycleBijectiveA g ↔
      ∀ k : ℕ, k < Fintype.card A ^ 4 → Function.Injective (globalMapA (n := k + 1) g) := by
  rw [cycleBijectiveA_iff_upTo g]
  constructor
  · intro h k hk
    exact h (k + 1) (Nat.succ_pos k) (by omega)
  · intro h m hm hmle
    obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
    exact h k (by omega)

/-- **Cycle-bijectivity is decidable** over a finite alphabet: the infinite family of
conditions is equivalent to a bounded conjunction of injectivity tests. -/
instance decidableCycleBijectiveA [Fintype A] [DecidableEq A] (g : A → A → A → A) :
    Decidable (CycleBijectiveA g) :=
  decidable_of_iff _ (cycleBijectiveA_iff_upTo' g).symm

/-- Decidability of cycle-bijectivity for ternary rules. -/
instance decidableCycleBijective (g : LocalRule) : Decidable (CycleBijective g) :=
  decidableCycleBijectiveA (A := Alph) g



end TernaryReversible
end Cryptography


