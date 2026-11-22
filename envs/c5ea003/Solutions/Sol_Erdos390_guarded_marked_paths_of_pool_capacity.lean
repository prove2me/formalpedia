-- Prove2me | solution 1 for Erdos390.guarded_marked_paths_of_pool_capacity
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-09-16T17:01:17.903341+00:00
-- url     : https://prove2.me/submissions/ba4a034d-c1e2-43ac-a6c2-ff2b9027d9dd

import Definitions.Def_erdos390_marked_bank_paths

open Erdos390.WholePaper

/- Finite matching argument adapted from BankOrdinaryPoolMatching.lean and
BankBottomPoolMatching.lean, Shouqiao Wang, erdos, pinned commit
61325b10bbdc29f4fb5e0618b414b9f2189333ad. -/
private theorem disjoint_pool_assignment
    {Request Pool : Type*} [Fintype Request] [DecidableEq Pool]
    (poolOf : Request → Pool) (available : Pool → Finset ℕ)
    (hcapacity : ∀ p, Fintype.card {r : Request // poolOf r = p} ≤ (available p).card)
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (available p) (available q)) :
    ∃ marker : Request → ℕ, Function.Injective marker ∧
      ∀ r, marker r ∈ available (poolOf r) := by
  classical
  let E : (p : Pool) → {r : Request // poolOf r = p} ↪ ↑(available p) := fun p ↦
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      simpa only [Fintype.card_coe] using hcapacity p))
  let label : Request → Σ p : Pool, {r : Request // poolOf r = p} :=
    fun r ↦ ⟨poolOf r, ⟨r, rfl⟩⟩
  let choose : (Σ p : Pool, {r : Request // poolOf r = p}) → ℕ :=
    fun r ↦ (E r.1 r.2).1
  have hlabel : Function.Injective label := by
    intro r s heq
    exact congrArg (fun x : Σ p : Pool, {r : Request // poolOf r = p} ↦ x.2.1) heq
  have hchoose : Function.Injective choose := by
    rintro ⟨p, r⟩ ⟨q, s⟩ heq
    by_cases hpq : p = q
    · subst q
      have he : E p r = E p s := Subtype.ext heq
      have hrs := (E p).injective he
      subst s
      rfl
    · have hr : choose ⟨p, r⟩ ∈ available p := (E p r).2
      have hs : choose ⟨p, r⟩ ∈ available q := by
        rw [heq]
        exact (E q s).2
      exact False.elim ((Finset.disjoint_left.mp (hdisjoint p q hpq)) hr hs)
  exact ⟨choose ∘ label, hchoose.comp hlabel, fun r ↦ (E (poolOf r) ⟨r, rfl⟩).2⟩

theorem solution
    {Pool : Type*} [DecidableEq Pool]
    (P : Finset ℕ) (β : ↑P → ℕ)
    (steps : SignedBankSlot β → ℕ)
    (core : SignedBankSlot β → ℕ → ℕ)
    (scale : (g : SignedBankSlot β) → Fin (steps g) → ℕ)
    (height : ℕ)
    (poolOf : (Σ g : SignedBankSlot β, Fin (steps g)) → Pool)
    (available : Pool → Finset ℕ)
    (ambient forbidden : Finset ℕ)
    (hstart : ∀ g, core g 0 = g.1.1)
    (hfinish : ∀ g, core g (steps g) = 1)
    (hcore : ∀ g i, i ≤ steps g → 0 < core g i)
    (hscale : ∀ g i, 0 < scale g i)
    (hsource : ∀ g i, scale g i * core g i.1 ≤ height)
    (htarget : ∀ g i, scale g i * core g (i.1 + 1) ≤ height)
    (hcapacity : ∀ p,
      Fintype.card {r : (Σ g : SignedBankSlot β, Fin (steps g)) // poolOf r = p} ≤
        (available p).card)
    (hdisjoint : ∀ p q, p ≠ q → Disjoint (available p) (available q))
    (hprime : ∀ p q, q ∈ available p → q.Prime)
    (hlarge : ∀ p q, q ∈ available p → height < q)
    (hlegal : ∀ g (i : Fin (steps g)) q,
      q ∈ available (poolOf ⟨g, i⟩) → ∀ b : Bool,
        q * (scale g i * core g (if b then i.1 + 1 else i.1)) ∈ ambient)
    (hguard : ∀ g (i : Fin (steps g)) q,
      q ∈ available (poolOf ⟨g, i⟩) → ∀ b : Bool,
        q * (scale g i * core g (if b then i.1 + 1 else i.1)) ∉ forbidden) :
    ∃ R : MarkedBankPaths P β,
      R.steps = steps ∧ R.core = core ∧ HEq R.scale scale ∧ R.height = height ∧
      ∀ g b, R.signedState g b ⊆ ambient ∧ Disjoint forbidden (R.signedState g b) := by
  classical
  obtain ⟨marker, hinjective, hmem⟩ :=
    disjoint_pool_assignment poolOf available hcapacity hdisjoint
  let R : MarkedBankPaths P β := {
    steps := steps
    core := core
    scale := scale
    marker := marker
    height := height
    core_start := hstart
    core_finish := hfinish
    core_pos := hcore
    scale_pos := hscale
    marker_prime := fun r ↦ hprime _ _ (hmem r)
    marker_injective := hinjective
    marker_large := fun r ↦ hlarge _ _ (hmem r)
    source_small := hsource
    target_small := htarget
  }
  have hendpointLegal (g : SignedBankSlot β) (b : Bool) (i : Fin (steps g)) :
      R.endpoint g b i ∈ ambient := hlegal g i _ (hmem ⟨g, i⟩) b
  have hendpointGuard (g : SignedBankSlot β) (b : Bool) (i : Fin (steps g)) :
      R.endpoint g b i ∉ forbidden := hguard g i _ (hmem ⟨g, i⟩) b
  have hdown (g : SignedBankSlot β) (b : Bool) :
      R.downwardState g b ⊆ ambient ∧ Disjoint forbidden (R.downwardState g b) := by
    constructor
    · intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact hendpointLegal g b i
    · apply Finset.disjoint_left.mpr
      intro a ha hb
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hb
      exact hendpointGuard g b i ha
  refine ⟨R, rfl, rfl, HEq.rfl, rfl, ?_⟩
  intro g b
  rcases g with ⟨p, i | i⟩
  · exact hdown _ (!b)
  · exact hdown _ b
