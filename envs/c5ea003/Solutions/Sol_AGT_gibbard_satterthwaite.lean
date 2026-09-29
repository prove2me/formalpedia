-- Prove2me | solution 1 for AGT.gibbard_satterthwaite
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-12T19:32:14.044507+00:00
-- url     : https://prove2.me/submissions/f196aafa-cb3c-4522-b0f8-36bc301d86b2

import Definitions.Def_agt_social
import Theorems.Thm_AGT_arrow_theorem
import Theorems.Thm_AGT_ic_iff_monotone
import Mathlib.Tactic

/-!
# The Gibbard–Satterthwaite theorem

Theorem 9.8 of *Algorithmic Game Theory*, derived from Arrow's theorem
(Theorem 9.3) through the top-set extension of Definition 9.9.

Given an incentive compatible onto social choice function `f`, the social
welfare function `swfOf f` is defined by: `a` beats `b` socially iff `a ≠ b`
and `f` elects `a` on the profile obtained from `P` by moving `a` and `b` to
the top of every ballot (preserving their relative order).  Lemmas 9.10 and
9.11 say that this is a social welfare function satisfying unanimity and
independence of irrelevant alternatives; Arrow's theorem then provides a
dictator, which is shown to be a dictator for `f` as well.
-/

namespace AGT

variable {A ι : Type*}

/-- `topSet S r` moves the alternatives of `S` to the top of the ballot `r`,
preserving the relative order inside `S` and inside its complement. -/
private def topSet (S : A → Prop) (r : A → A → Prop) : A → A → Prop :=
  fun x y => (S x ∧ ¬ S y) ∨ ((S x ↔ S y) ∧ r x y)

/-- The two-element set `{a, b}`. -/
private def pairSet (a b : A) : A → Prop := fun z => z = a ∨ z = b

/-- The three-element set `{a, b, c}`. -/
private def tripleSet (a b c : A) : A → Prop := fun z => z = a ∨ z = b ∨ z = c

private theorem isSTO_topSet {S : A → Prop} {r : A → A → Prop}
    (hr : IsStrictTotalOrder A r) : IsStrictTotalOrder A (topSet S r) := by
  haveI := hr
  haveI : IsIrrefl A (topSet S r) := by
    refine ⟨fun x hx => ?_⟩
    rcases hx with ⟨h1, h2⟩ | ⟨_, h2⟩
    · exact h2 h1
    · exact irrefl_of r x h2
  haveI : IsTrans A (topSet S r) := by
    refine ⟨fun x y z hxy hyz => ?_⟩
    rcases hxy with ⟨hx, hy⟩ | ⟨hxy', hr1⟩
    · rcases hyz with ⟨hy', _⟩ | ⟨hyz', _⟩
      · exact absurd hy' hy
      · exact Or.inl ⟨hx, fun hz => hy (hyz'.2 hz)⟩
    · rcases hyz with ⟨hy, hz⟩ | ⟨hyz', hr2⟩
      · exact Or.inl ⟨hxy'.2 hy, hz⟩
      · exact Or.inr ⟨hxy'.trans hyz', trans_of r hr1 hr2⟩
  haveI : IsTrichotomous A (topSet S r) := by
    refine ⟨fun x y h1 h2 => ?_⟩
    by_cases hx : S x
    · by_cases hy : S y
      · refine trichotomous_of r x y |>.resolve_left ?_ |>.resolve_right ?_
        · exact fun h => h1 (Or.inr ⟨iff_of_true hx hy, h⟩)
        · exact fun h => h2 (Or.inr ⟨iff_of_true hy hx, h⟩)
      · exact absurd (Or.inl ⟨hx, hy⟩) h1
    · by_cases hy : S y
      · exact absurd (Or.inl ⟨hy, hx⟩) h2
      · refine trichotomous_of r x y |>.resolve_left ?_ |>.resolve_right ?_
        · exact fun h => h1 (Or.inr ⟨iff_of_false hx hy, h⟩)
        · exact fun h => h2 (Or.inr ⟨iff_of_false hy hx, h⟩)
  exact {}

private theorem topSet_same {S : A → Prop} {r : A → A → Prop} {x y : A}
    (h : S x ↔ S y) : topSet S r x y ↔ r x y := by
  constructor
  · rintro (⟨h1, h2⟩ | ⟨_, h2⟩)
    · exact absurd (h.1 h1) h2
    · exact h2
  · exact fun hr => Or.inr ⟨h, hr⟩

private theorem topSet_in_out {S : A → Prop} {r : A → A → Prop} {x y : A}
    (hx : S x) (hy : ¬ S y) : topSet S r x y := Or.inl ⟨hx, hy⟩

private theorem not_topSet_out_in {S : A → Prop} {r : A → A → Prop} {x y : A}
    (hx : S x) (hy : ¬ S y) : ¬ topSet S r y x := by
  rintro (⟨h1, _⟩ | ⟨h1, _⟩)
  · exact hy h1
  · exact hy (h1.2 hx)

private theorem flip_iff {r r' : A → A → Prop} (hr : IsStrictTotalOrder A r)
    (hr' : IsStrictTotalOrder A r') {a b : A} (hab : a ≠ b) (h : r a b ↔ r' a b) :
    r b a ↔ r' b a := by
  haveI := hr
  haveI := hr'
  constructor
  · intro hba
    rcases trichotomous_of r' b a with h1 | h1 | h1
    · exact h1
    · exact absurd h1 (Ne.symm hab)
    · exact absurd (h.2 h1) (asymm_of r hba)
  · intro hba
    rcases trichotomous_of r b a with h1 | h1 | h1
    · exact h1
    · exact absurd h1 (Ne.symm hab)
    · exact absurd (h.1 h1) (asymm_of r' hba)

private theorem pairSet_comm (a b : A) : pairSet a b = pairSet b a := by
  funext z
  exact propext (by simp only [pairSet]; tauto)

section Choice

variable [Fintype ι] [DecidableEq ι] {f : (ι → A → A → Prop) → A}

/-- Moving from one profile to another one voter at a time: if no voter can,
at the pair `(w, v)`, rank `w` above `v` in `P` while ranking `v` above `w`
in `Q`, then the outcome `w` is preserved. -/
private theorem hybrid (hmono : SCFMonotone f) {P Q : ι → A → A → Prop}
    (hP : IsPrefProfile P) (hQ : IsPrefProfile Q) {w : A}
    (hcond : ∀ j v, v ≠ w → ¬ (P j w v ∧ Q j v w)) (hfP : f P = w) : f Q = w := by
  classical
  have key : ∀ S : Finset ι, f (fun j => if j ∈ S then Q j else P j) = w := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa using hfP
    | insert j S hj ih =>
        set R : ι → A → A → Prop := fun k => if k ∈ S then Q k else P k with hR
        have hRpref : IsPrefProfile R := by
          intro k
          by_cases hk : k ∈ S
          · simpa [hR, hk] using hQ k
          · simpa [hR, hk] using hP k
        have hRj : R j = P j := by simp [hR, hj]
        have hupd : (fun k => if k ∈ insert j S then Q k else P k)
            = Function.update R j (Q j) := by
          funext k
          by_cases hk : k = j
          · subst hk; simp [hR, hj]
          · simp [hR, Function.update_of_ne hk, Finset.mem_insert, hk]
        rw [hupd]
        by_cases hchange : f R = f (Function.update R j (Q j))
        · rw [← hchange]; exact ih
        · obtain ⟨h1, h2⟩ := hmono R hRpref j (Q j) (hQ j) hchange
          rw [ih] at h1 h2 hchange
          rw [hRj] at h1
          exact absurd ⟨h1, h2⟩ (hcond j _ (Ne.symm hchange))
  have h := key Finset.univ
  simpa using h

/-- If every voter ranks `a` first, `f` elects `a`. -/
private theorem f_unanimous (hmono : SCFMonotone f) (honto : SCFOnto f)
    {P : ι → A → A → Prop} (hP : IsPrefProfile P) {a : A}
    (htop : ∀ i x, x ≠ a → P i a x) : f P = a := by
  obtain ⟨Q, hQ, hQa⟩ := honto a
  refine hybrid hmono hQ hP (w := a) ?_ hQa
  rintro j v hv ⟨-, h2⟩
  haveI := hP j
  exact absurd h2 (asymm_of (P j) (htop j v hv))

/-- Weak Pareto: an alternative that every voter ranks below `a` is not elected. -/
private theorem f_ne_of_dominated (hmono : SCFMonotone f) (honto : SCFOnto f)
    {P : ι → A → A → Prop} (hP : IsPrefProfile P) {a c : A} (hac : a ≠ c)
    (h : ∀ i, P i a c) : f P ≠ c := by
  intro hc
  have hP' : IsPrefProfile (fun i => topSet (fun z => z = a) (P i)) := fun i =>
    isSTO_topSet (hP i)
  have h1 : f (fun i => topSet (fun z => z = a) (P i)) = a :=
    f_unanimous hmono honto hP' (fun _ x hx => topSet_in_out rfl hx)
  have h2 : f (fun i => topSet (fun z => z = a) (P i)) = c := by
    refine hybrid hmono hP hP' (w := c) ?_ hc
    rintro j v hv ⟨g1, g2⟩
    haveI := hP j
    by_cases hva : v = a
    · subst hva
      exact absurd g1 (asymm_of (P j) (h j))
    · have hvc : P j v c := by
        refine (topSet_same ?_).1 g2
        exact iff_of_false hva (Ne.symm hac)
      exact absurd hvc (asymm_of (P j) g1)
  exact hac (h1 ▸ h2)

/-- The winner on a profile whose ballots all have top set `S` belongs to `S`. -/
private theorem f_mem_topSet (hmono : SCFMonotone f) (honto : SCFOnto f)
    {P : ι → A → A → Prop} (hP : IsPrefProfile P) {S : A → Prop} {a : A} (hSa : S a) :
    S (f (fun i => topSet S (P i))) := by
  by_contra hc
  have hne : a ≠ f (fun i => topSet S (P i)) := by
    rintro rfl
    exact hc hSa
  exact f_ne_of_dominated hmono honto (fun i => isSTO_topSet (hP i)) hne
    (fun i => topSet_in_out hSa hc) rfl

/-- Lifting a set containing the winner to the top of every ballot does not
change the winner. -/
private theorem lift_keeps (hmono : SCFMonotone f) {P : ι → A → A → Prop}
    (hP : IsPrefProfile P) {T : A → Prop} {w : A} (hw : T w) (hfw : f P = w) :
    f (fun i => topSet T (P i)) = w := by
  refine hybrid hmono hP (fun i => isSTO_topSet (hP i)) (w := w) ?_ hfw
  rintro j v hv ⟨g1, g2⟩
  haveI := hP j
  have : P j v w := by
    rcases g2 with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact absurd hw h2
    · exact h2
  exact absurd this (asymm_of (P j) g1)

/-- Shrinking the top set, keeping the winner inside it, does not change the winner. -/
private theorem drop_keeps (hmono : SCFMonotone f) {P : ι → A → A → Prop}
    (hP : IsPrefProfile P) {S T : A → Prop} (hTS : ∀ z, T z → S z) {w : A} (hw : T w)
    (hfw : f (fun i => topSet S (P i)) = w) : f (fun i => topSet T (P i)) = w := by
  refine hybrid hmono (fun i => isSTO_topSet (hP i)) (fun i => isSTO_topSet (hP i))
    (w := w) ?_ hfw
  rintro j v hv ⟨g1, g2⟩
  haveI := hP j
  have hTv : T v := by
    rcases g2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact h1.2 hw
  have hPvw : P j v w := by
    rcases g2 with ⟨-, h2⟩ | ⟨-, h2⟩
    · exact absurd hw h2
    · exact h2
  have hPwv : P j w v :=
    (topSet_same (iff_of_true (hTS w hw) (hTS v hTv))).1 g1
  exact absurd hPvw (asymm_of (P j) hPwv)

/-- Two profiles whose ballots agree inside the top set `T` elect the same
alternative of `T`. -/
private theorem iia_transfer (hmono : SCFMonotone f) {P Q : ι → A → A → Prop}
    (hP : IsPrefProfile P) (hQ : IsPrefProfile Q) {T : A → Prop} {w : A} (hw : T w)
    (hagree : ∀ j x y, T x → T y → (P j x y ↔ Q j x y))
    (hf : f (fun i => topSet T (P i)) = w) : f (fun i => topSet T (Q i)) = w := by
  refine hybrid hmono (fun i => isSTO_topSet (hP i)) (fun i => isSTO_topSet (hQ i))
    (w := w) ?_ hf
  rintro j v hv ⟨g1, g2⟩
  haveI := hQ j
  have hTv : T v := by
    rcases g2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact h1
    · exact h1.2 hw
  have hQvw : Q j v w := (topSet_same (iff_of_true hTv hw)).1 g2
  have hPwv : P j w v := (topSet_same (iff_of_true hw hTv)).1 g1
  exact absurd ((hagree j w v hw hTv).1 hPwv) (asymm_of (Q j) hQvw)

/-- **Definition 9.9**: the social welfare function extending `f`. -/
private def swfOf (f : (ι → A → A → Prop) → A) (P : ι → A → A → Prop) (a b : A) : Prop :=
  a ≠ b ∧ f (fun i => topSet (pairSet a b) (P i)) = a

/-- **Lemma 9.10**: `swfOf f` is a social welfare function. -/
private theorem isSWF_swfOf (hmono : SCFMonotone f) (honto : SCFOnto f) :
    IsSWF (swfOf f (ι := ι)) := by
  intro P hP
  haveI : IsIrrefl A (swfOf f P) := ⟨fun x hx => hx.1 rfl⟩
  haveI : IsTrichotomous A (swfOf f P) := by
    refine ⟨fun x y h1 h2 => ?_⟩
    by_contra hxy
    have hmem : pairSet x y (f (fun i => topSet (pairSet x y) (P i))) :=
      f_mem_topSet hmono honto hP (Or.inl rfl)
    rcases hmem with h | h
    · exact h1 ⟨hxy, h⟩
    · refine h2 ⟨Ne.symm hxy, ?_⟩
      rw [pairSet_comm y x]
      exact h
  haveI : IsTrans A (swfOf f P) := by
    refine ⟨fun a b c hab hbc => ?_⟩
    obtain ⟨hab1, hab2⟩ := hab
    obtain ⟨hbc1, hbc2⟩ := hbc
    have hac : a ≠ c := by
      rintro rfl
      rw [pairSet_comm a b] at hab2
      exact hab1 (hab2.symm.trans hbc2)
    refine ⟨hac, ?_⟩
    have hmem : tripleSet a b c (f (fun i => topSet (tripleSet a b c) (P i))) :=
      f_mem_topSet hmono honto hP (Or.inl rfl)
    have hsubAB : ∀ z, pairSet a b z → tripleSet a b c z := by
      rintro z (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    have hsubBC : ∀ z, pairSet b c z → tripleSet a b c z := by
      rintro z (rfl | rfl)
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr rfl)
    have hsubAC : ∀ z, pairSet a c z → tripleSet a b c z := by
      rintro z (rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    rcases hmem with h | h | h
    · exact drop_keeps hmono hP hsubAC (Or.inl rfl) h
    · exfalso
      have hb : f (fun i => topSet (pairSet a b) (P i)) = b :=
        drop_keeps hmono hP hsubAB (Or.inr rfl) h
      exact hab1 (hab2.symm.trans hb)
    · exfalso
      have hc : f (fun i => topSet (pairSet b c) (P i)) = c :=
        drop_keeps hmono hP hsubBC (Or.inr rfl) h
      exact hbc1 (hbc2.symm.trans hc)
  exact {}

/-- **Lemma 9.11 (unanimity)**. -/
private theorem unanimity_swfOf (hmono : SCFMonotone f) (honto : SCFOnto f) :
    SWFUnanimity (swfOf f (ι := ι)) := by
  intro r hr a b
  haveI := hr
  have hconst : IsPrefProfile (fun _ : ι => r) := fun _ => hr
  have hlift : IsPrefProfile (fun _ : ι => topSet (pairSet a b) r) := fun _ =>
    isSTO_topSet hr
  constructor
  · rintro ⟨hab, hf⟩
    by_contra hr'
    have hba : r b a := by
      rcases trichotomous_of r a b with h | h | h
      · exact absurd h hr'
      · exact absurd h hab
      · exact h
    have : f (fun _ : ι => topSet (pairSet a b) r) = b := by
      refine f_unanimous hmono honto hlift (fun _ x hx => ?_)
      by_cases hxa : x = a
      · subst hxa
        refine (topSet_same ?_).2 hba
        exact iff_of_true (Or.inr rfl) (Or.inl rfl)
      · exact topSet_in_out (Or.inr rfl) (by simp only [pairSet]; tauto)
    exact hab (hf.symm.trans this)
  · intro hrab
    have hab : a ≠ b := by
      rintro rfl
      exact irrefl_of r a hrab
    refine ⟨hab, ?_⟩
    refine f_unanimous hmono honto hlift (fun _ x hx => ?_)
    by_cases hxb : x = b
    · subst hxb
      refine (topSet_same ?_).2 hrab
      exact iff_of_true (Or.inl rfl) (Or.inr rfl)
    · exact topSet_in_out (Or.inl rfl) (by simp only [pairSet]; tauto)

/-- **Lemma 9.11 (IIA)**. -/
private theorem iia_swfOf (hmono : SCFMonotone f) :
    SWFIIA (swfOf f (ι := ι)) := by
  intro P Q hP hQ a b hagree
  by_cases hab : a ≠ b
  · have key : ∀ (R R' : ι → A → A → Prop), IsPrefProfile R → IsPrefProfile R' →
        (∀ i, R i a b ↔ R' i a b) →
        f (fun i => topSet (pairSet a b) (R i)) = a →
        f (fun i => topSet (pairSet a b) (R' i)) = a := by
      intro R R' hR hR' hag hf
      refine iia_transfer hmono hR hR' (T := pairSet a b) (Or.inl rfl) ?_ hf
      rintro j x y (rfl | rfl) (rfl | rfl)
      · haveI := hR j
        haveI := hR' j
        exact iff_of_false (irrefl_of (R j) _) (irrefl_of (R' j) _)
      · exact hag j
      · exact flip_iff (hR j) (hR' j) hab (hag j)
      · haveI := hR j
        haveI := hR' j
        exact iff_of_false (irrefl_of (R j) _) (irrefl_of (R' j) _)
    constructor
    · rintro ⟨-, hf⟩
      exact ⟨hab, key P Q hP hQ hagree hf⟩
    · rintro ⟨-, hf⟩
      exact ⟨hab, key Q P hQ hP (fun i => (hagree i).symm) hf⟩
  · simp only [not_not] at hab
    subst hab
    exact iff_of_false (fun h => h.1 rfl) (fun h => h.1 rfl)

end Choice

end AGT

open AGT in
/-- **Theorem 9.8 of *Algorithmic Game Theory* (Gibbard–Satterthwaite)**:
every incentive compatible social choice function onto more than two
alternatives is a dictatorship. -/
theorem solution {A ι : Type*} [Fintype A] [Fintype ι]
    [DecidableEq ι] (hA : 2 < Fintype.card A)
    (f : (ι → A → A → Prop) → A) (hic : IncentiveCompatible f)
    (honto : SCFOnto f) :
    ∃ i : ι, SCFDictator f i := by
  classical
  have hmono : SCFMonotone f := (AGT.ic_iff_monotone f).1 hic
  have hAne : Nonempty A := Fintype.card_pos_iff.1 (by omega)
  by_cases hι : Nonempty ι
  · obtain ⟨i, hi⟩ := AGT.arrow_theorem hA (AGT.swfOf f) (AGT.isSWF_swfOf hmono honto)
      (AGT.unanimity_swfOf hmono honto) (AGT.iia_swfOf hmono)
    refine ⟨i, fun P hP a htop => ?_⟩
    by_contra hfa
    have hne : a ≠ f P := fun h => hfa h.symm
    have h1 : AGT.swfOf f P a (f P) := (hi P hP a (f P)).2 (htop _ (Ne.symm hne))
    have h2 : f (fun j => AGT.topSet (AGT.pairSet a (f P)) (P j)) = f P :=
      AGT.lift_keeps hmono hP (Or.inr rfl) rfl
    exact hne (h1.2.symm.trans h2)
  · exfalso
    have hemp : IsEmpty ι := not_nonempty_iff.1 hι
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (α := A) (by omega)
    obtain ⟨P, -, hPa⟩ := honto a
    obtain ⟨Q, -, hQb⟩ := honto b
    have : P = Q := funext fun i => hemp.elim i
    exact hab (hPa ▸ this ▸ hQb ▸ rfl)
