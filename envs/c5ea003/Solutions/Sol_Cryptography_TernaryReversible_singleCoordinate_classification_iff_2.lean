-- Prove2me | solution 2 for Cryptography.TernaryReversible.singleCoordinate_classification_iff
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:13:10.905743+00:00
-- url     : https://prove2.me/submissions/ca210fdc-7a28-496f-99ae-fa18cc5e7c62

import Mathlib
import Definitions.Def_Cryptography_TernaryReversible_Core
import Definitions.Def_Cryptography_TernaryReversible_General

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Cryptography/TernaryReversible/Core.lean ====
/-!
# Reversible ternary radius-one cellular automata: core framework

Alphabet `Fin 3`, local rules `g : Fin 3 → Fin 3 → Fin 3 → Fin 3` (a radius-one,
window-three rule) and the induced *global maps* on the finite cycle `ZMod n`:

`globalMap g s i = g (s (i-1)) (s i) (s (i+1))`.

A rule is **cycle-bijective** when its global map is bijective on *every* nonempty
finite cycle.  This file develops the general tools:

* `globalMap`, `CycleBijective`, `SingleCoordinatePerm`;
* `cycleBijective_of_decoder3` / `cycleBijective_of_decoder4R`: a *local decoder*
  (a local inverse rule, of window 3 resp. window 4) forces cycle-bijectivity on
  every cycle length simultaneously — this is the engine used everywhere else;
* closure properties: post-composition with a permutation of the alphabet, and
  spatial reflection, preserve cycle-bijectivity;
* `cycleBijective_of_singleCoordinatePerm`: the "trivial" rules
  `g = σ ∘ (one coordinate)` are cycle-bijective (the *easy* half of the
  classification claim under test);
* `diag_bijective_of_cycleBijective`: a first necessary condition.

The hard half of the classification claim (that these are the *only*
cycle-bijective rules) is **false**; see `Cryptography.TernaryReversible.Refutation`.
-/

namespace Cryptography
namespace TernaryReversible

-- [dropped: platform already declares Alph]
/-- The alphabet is literally `Fin 3`. -/
theorem Alph_eq_Fin3 : Alph = Fin 3 := rfl

-- [dropped: platform already declares LocalRule]
-- [dropped: platform already declares globalMap]
-- [dropped: platform already declares CycleBijective]
-- [dropped: platform already declares SingleCoordinatePerm]
-- [dropped: platform already declares DependsLeft]
-- [dropped: platform already declares DependsMiddle]
-- [dropped: platform already declares DependsRight]
/-- A rule that genuinely depends on two of its three arguments cannot be a single
coordinate followed by a permutation. -/
theorem not_singleCoordinatePerm_of_twoDeps {g : LocalRule}
    (h : (DependsLeft g ∧ DependsMiddle g) ∨ (DependsLeft g ∧ DependsRight g) ∨
      (DependsMiddle g ∧ DependsRight g)) : ¬ SingleCoordinatePerm g := by
  rintro ⟨σ, rfl | rfl | rfl⟩
  · have hm : ¬ DependsMiddle (fun (a : Alph) (_ _ : Alph) => σ a) := by
      rintro ⟨a, b, b', c, hne⟩; exact hne rfl
    have hr : ¬ DependsRight (fun (a : Alph) (_ _ : Alph) => σ a) := by
      rintro ⟨a, b, c, c', hne⟩; exact hne rfl
    rcases h with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩
    · exact hm h2
    · exact hr h2
    · exact hm h1
  · have hl : ¬ DependsLeft (fun (_ : Alph) (b : Alph) (_ : Alph) => σ b) := by
      rintro ⟨a, a', b, c, hne⟩; exact hne rfl
    have hr : ¬ DependsRight (fun (_ : Alph) (b : Alph) (_ : Alph) => σ b) := by
      rintro ⟨a, b, c, c', hne⟩; exact hne rfl
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩
    · exact hl h1
    · exact hl h1
    · exact hr h2
  · have hl : ¬ DependsLeft (fun (_ _ : Alph) (c : Alph) => σ c) := by
      rintro ⟨a, a', b, c, hne⟩; exact hne rfl
    have hm : ¬ DependsMiddle (fun (_ _ : Alph) (c : Alph) => σ c) := by
      rintro ⟨a, b, b', c, hne⟩; exact hne rfl
    rcases h with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
    · exact hl h1
    · exact hl h1
    · exact hm h1

/-! ## Local decoders force bijectivity on all cycles -/

/-- The pointwise decoding identity on a cycle: a window-3 decoder `d` for `g`
reconstructs every cell of a configuration from three consecutive cells of its image,
for every cycle length. -/
theorem decoder3_apply {g d : LocalRule}
    (h : ∀ v w x y z, d (g v w x) (g w x y) (g x y z) = x) {n : ℕ} (u : ZMod n → Alph)
    (i : ZMod n) :
    d (globalMap g u (i - 1)) (globalMap g u i) (globalMap g u (i + 1)) = u i := by
  have e1 : globalMap g u (i - 1) = g (u (i - 1 - 1)) (u (i - 1)) (u i) := by
    simp [globalMap, sub_add_cancel]
  have e3 : globalMap g u (i + 1) = g (u i) (u (i + 1)) (u (i + 1 + 1)) := by
    simp [globalMap, add_sub_cancel_right]
  rw [e1, e3]
  exact h _ _ _ _ _

/-- **Window-3 decoder criterion.** If a local rule `d` reconstructs the middle cell
from three consecutive output cells, then `g` is bijective on every finite cycle.
Note the decoder identity is a statement about *words*, yet it yields bijectivity
for *all* cycle lengths at once, including lengths shorter than the window. -/
theorem cycleBijective_of_decoder3 (g d : LocalRule)
    (h : ∀ v w x y z, d (g v w x) (g w x y) (g x y z) = x) : CycleBijective g := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [← Finite.injective_iff_bijective]
  intro s t hst
  funext i
  rw [← decoder3_apply h s i, ← decoder3_apply h t i, hst]

/-- A rule that decodes *itself* induces an involution on every finite cycle. -/
theorem globalMap_involutive_of_selfDecoder {g : LocalRule}
    (h : ∀ v w x y z, g (g v w x) (g w x y) (g x y z) = x) {n : ℕ} (s : ZMod n → Alph) :
    globalMap g (globalMap g s) = s := by
  funext i
  exact decoder3_apply h s i

/-- **Window-4 (right-looking) decoder criterion.** If a rule `d` reconstructs the
leftmost cell of a window of six from the four outputs it determines, then `g` is
bijective on every finite cycle.  Such a decoder is an inverse cellular automaton
of neighbourhood `{1,2,3,4}`, i.e. of radius at least two. -/
theorem cycleBijective_of_decoder4R (g : LocalRule) (d : Alph → Alph → Alph → Alph → Alph)
    (h : ∀ x₀ x₁ x₂ x₃ x₄ x₅,
      d (g x₀ x₁ x₂) (g x₁ x₂ x₃) (g x₂ x₃ x₄) (g x₃ x₄ x₅) = x₀) :
    CycleBijective g := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [← Finite.injective_iff_bijective]
  intro s t hst
  funext i
  have key : ∀ u : ZMod n → Alph,
      d (globalMap g u (i + 1)) (globalMap g u (i + 2)) (globalMap g u (i + 3))
        (globalMap g u (i + 4)) = u i := by
    intro u
    have e : ∀ k : ZMod n,
        globalMap g u (k + 1) = g (u k) (u (k + 1)) (u (k + 2)) := by
      intro k
      have h1 : k + 1 - 1 = k := by ring
      have h2 : k + 1 + 1 = k + 2 := by ring
      simp only [globalMap, h1, h2]
    have e1 := e i
    have e2 : globalMap g u (i + 2) = g (u (i + 1)) (u (i + 2)) (u (i + 3)) := by
      have := e (i + 1)
      rw [show i + 1 + 1 = i + 2 by ring, show i + 1 + 2 = i + 3 by ring] at this
      exact this
    have e3 : globalMap g u (i + 3) = g (u (i + 2)) (u (i + 3)) (u (i + 4)) := by
      have := e (i + 2)
      rw [show i + 2 + 1 = i + 3 by ring, show i + 2 + 2 = i + 4 by ring] at this
      exact this
    have e4 : globalMap g u (i + 4) = g (u (i + 3)) (u (i + 4)) (u (i + 5)) := by
      have := e (i + 3)
      rw [show i + 3 + 1 = i + 4 by ring, show i + 3 + 2 = i + 5 by ring] at this
      exact this
    rw [e1, e2, e3, e4]
    exact h _ _ _ _ _ _
  rw [← key s, ← key t, hst]

/-! ## Closure properties -/

/-- Post-composing a cycle-bijective rule with a bijection of the alphabet keeps it
cycle-bijective. -/
theorem cycleBijective_comp {g : LocalRule} {f : Alph → Alph} (hf : Function.Bijective f)
    (hg : CycleBijective g) : CycleBijective (fun a b c => f (g a b c)) := by
  intro n hn
  have hcomp : globalMap (n := n) (fun a b c => f (g a b c))
      = (fun s => (fun i => f (s i))) ∘ globalMap (n := n) g := rfl
  rw [hcomp]
  refine Function.Bijective.comp ?_ (hg n hn)
  obtain ⟨hinj, hsurj⟩ := hf
  constructor
  · intro s t hst
    funext i
    exact hinj (congrFun hst i)
  · intro t
    choose finv hfinv using hsurj
    exact ⟨fun i => finv (t i), by funext i; simp [hfinv]⟩

/-- Cycle-bijectivity is invariant under relabelling the alphabet: it is a property of
the rule up to conjugation by a permutation. -/
theorem cycleBijective_conj {g : LocalRule} (σ : Equiv.Perm Alph) (hg : CycleBijective g) :
    CycleBijective (fun a b c => σ.symm (g (σ a) (σ b) (σ c))) := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hconj : globalMap (n := n) (fun a b c => σ.symm (g (σ a) (σ b) (σ c)))
      = (fun (u : ZMod n → Alph) (i : ZMod n) => σ.symm (u i)) ∘ globalMap (n := n) g ∘
        (fun (u : ZMod n → Alph) (i : ZMod n) => σ (u i)) := rfl
  rw [hconj]
  have hpost : Function.Bijective (fun (u : ZMod n → Alph) (i : ZMod n) => σ.symm (u i)) :=
    ⟨fun u v huv => funext fun i => σ.symm.injective (congrFun huv i),
      fun v => ⟨fun i => σ (v i), by funext i; simp⟩⟩
  have hpre : Function.Bijective (fun (u : ZMod n → Alph) (i : ZMod n) => σ (u i)) :=
    ⟨fun u v huv => funext fun i => σ.injective (congrFun huv i),
      fun v => ⟨fun i => σ.symm (v i), by funext i; simp⟩⟩
  exact hpost.comp ((hg n hn).comp hpre)

/-- Reflecting a rule in space (`a b c ↦ g c b a`) preserves cycle-bijectivity:
the global maps are conjugate by the index reflection `i ↦ -i`. -/
theorem cycleBijective_reflect {g : LocalRule} (hg : CycleBijective g) :
    CycleBijective (fun a b c => g c b a) := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  have hRR : ∀ s : ZMod n → Alph, (fun i : ZMod n => (fun j : ZMod n => s (-j)) (-i)) = s := by
    intro s; funext i; simp
  have hRbij : Function.Bijective (fun (s : ZMod n → Alph) (i : ZMod n) => s (-i)) := by
    constructor
    · intro s t hst
      funext i
      have := congrFun hst (-i)
      simpa using this
    · intro t
      exact ⟨fun i => t (-i), by funext i; simp⟩
  have hconj : globalMap (n := n) (fun a b c => g c b a)
      = (fun (u : ZMod n → Alph) (i : ZMod n) => u (-i)) ∘ globalMap (n := n) g ∘
        (fun (u : ZMod n → Alph) (i : ZMod n) => u (-i)) := by
    funext s i
    show g (s (i + 1)) (s i) (s (i - 1)) = g (s (-(-i - 1))) (s (-(-i))) (s (-(-i + 1)))
    rw [show -(-i - 1) = i + 1 by ring, show -(-i) = i by ring, show -(-i + 1) = i - 1 by ring]
  rw [hconj]
  exact hRbij.comp ((hg n hn).comp hRbij)

/-! ## The easy half of the classification claim -/

/-- A single coordinate followed by a permutation is cycle-bijective. -/
theorem cycleBijective_of_singleCoordinatePerm {g : LocalRule}
    (hg : SingleCoordinatePerm g) : CycleBijective g := by
  obtain ⟨σ, h | h | h⟩ := hg <;> subst h
  · -- `g a b c = σ a`: decode from the right output
    refine cycleBijective_of_decoder3 _ (fun _ _ z => σ.symm z) ?_
    intro v w x y z; simp
  · -- `g a b c = σ b`: decode from the middle output
    refine cycleBijective_of_decoder3 _ (fun _ y _ => σ.symm y) ?_
    intro v w x y z; simp
  · -- `g a b c = σ c`: decode from the left output
    refine cycleBijective_of_decoder3 _ (fun x _ _ => σ.symm x) ?_
    intro v w x y z; simp

/-! ## A necessary condition -/

/-- On the one-cell cycle the global map is `a ↦ g a a a`, so this "diagonal" map of a
cycle-bijective rule must be a permutation of the alphabet. -/
theorem diag_bijective_of_cycleBijective {g : LocalRule} (hg : CycleBijective g) :
    Function.Bijective (fun a : Alph => g a a a) := by
  have h1 := hg 1 one_pos
  have e : (fun a : Alph => g a a a)
      = (fun s : ZMod 1 → Alph => s 0) ∘ globalMap (n := 1) g ∘ (fun a _ => a) := by
    funext a
    rfl
  rw [e]
  have hfst : Function.Bijective (fun s : ZMod 1 → Alph => s 0) := by
    constructor
    · intro s t hst
      funext i
      rw [Subsingleton.elim i 0]
      exact hst
    · intro a; exact ⟨fun _ => a, rfl⟩
  have hconst : Function.Bijective (fun (a : Alph) (_ : ZMod 1) => a) := by
    constructor
    · intro a b hab; exact congrFun hab 0
    · intro s; exact ⟨s 0, by funext i; rw [Subsingleton.elim i 0]⟩
  exact hfst.comp (h1.comp hconst)

end TernaryReversible
end Cryptography
-- ==== upstream: Packages/Catalog/Cryptography/TernaryReversible/General.lean ====
/-!
# The size-two dichotomy for radius-one reversibility

Everything so far concerned the ternary alphabet.  This file identifies **exactly** for
which alphabets the single-coordinate classification claim is true.

For an arbitrary alphabet `A` we consider radius-one rules `g : A → A → A → A` with the
global maps `globalMapA g s i = g (s (i-1)) (s i) (s (i+1))` on the cycle `ZMod n`.

* If `A` has at least three elements `x₀, x₁, x₂` then the **conditional transposition**
  `twistRule x₀ x₁ x₂ a b c = if c = x₀ then (x₁ x₂)·b else b` is an involution on every
  finite cycle — the transposition fixes `x₀`, so the positions carrying `x₀` are visible
  in the output and the twist can be undone — while it uses two cells of its window.
  Hence the claim fails for *every* alphabet of size `≥ 3`; the ternary counterexamples
  of `Refutation.lean` are the smallest instance of a universal phenomenon.
* For the binary alphabet the claim is **true**: bijectivity on the cycles of length
  `1, 2, 3, 4` already forces a rule on `Fin 2` to be a single coordinate followed by a
  permutation (an exhaustive verification over all `2⁸ = 256` binary rules).

The two results combine into `singleCoordinate_classification_iff`: for `A = Fin q` the
classification claim holds **iff** `q ≤ 2`.

## Main results

* `twistRule_involution`, `twistRule_cycleBijectiveA`, `claim_fails_of_three_elements`;
* `binary_classification`;
* `singleCoordinate_classification_iff`.
-/

namespace Cryptography
namespace TernaryReversible

/-! ## The general framework -/

variable {A : Type}

-- [dropped: platform already declares globalMapA]
-- [dropped: platform already declares CycleBijectiveA]
-- [dropped: platform already declares SingleCoordinatePermA]
-- [dropped: platform already declares decidableSingleCoordinatePermA]
/-- The ternary notions of `Core.lean` are the special case `A = Alph`. -/
theorem cycleBijective_iff_general (g : LocalRule) : CycleBijective g ↔ CycleBijectiveA g :=
  Iff.rfl

-- [dropped: platform already declares DependsMiddleA]
-- [dropped: platform already declares DependsRightA]
/-- A rule using both its middle and its right cell is not a single coordinate followed
by a permutation. -/
theorem not_singleCoordinatePermA_of_MR {g : A → A → A → A} (hm : DependsMiddleA g)
    (hr : DependsRightA g) : ¬ SingleCoordinatePermA g := by
  rintro ⟨σ, rfl | rfl | rfl⟩
  · obtain ⟨a, b, b', c, hne⟩ := hm; exact hne rfl
  · obtain ⟨a, b, c, c', hne⟩ := hr; exact hne rfl
  · obtain ⟨a, b, b', c, hne⟩ := hm; exact hne rfl

/-- **Window-3 decoder criterion**, general alphabet. -/
theorem cycleBijectiveA_of_decoder3 [Fintype A] (g d : A → A → A → A)
    (h : ∀ v w x y z, d (g v w x) (g w x y) (g x y z) = x) : CycleBijectiveA g := by
  intro n hn
  haveI : NeZero n := ⟨hn.ne'⟩
  rw [← Finite.injective_iff_bijective]
  intro s t hst
  funext i
  have key : ∀ u : ZMod n → A,
      d (globalMapA g u (i - 1)) (globalMapA g u i) (globalMapA g u (i + 1)) = u i := by
    intro u
    have e1 : globalMapA g u (i - 1) = g (u (i - 1 - 1)) (u (i - 1)) (u i) := by
      simp [globalMapA, sub_add_cancel]
    have e3 : globalMapA g u (i + 1) = g (u i) (u (i + 1)) (u (i + 1 + 1)) := by
      simp [globalMapA, add_sub_cancel_right]
    rw [e1, e3]
    exact h _ _ _ _ _
  rw [← key s, ← key t, hst]

/-- A self-decoding rule is an involution on every finite cycle. -/
theorem globalMapA_involutive {g : A → A → A → A}
    (h : ∀ v w x y z, g (g v w x) (g w x y) (g x y z) = x) {n : ℕ} (s : ZMod n → A) :
    globalMapA g (globalMapA g s) = s := by
  funext i
  have e1 : globalMapA g s (i - 1) = g (s (i - 1 - 1)) (s (i - 1)) (s i) := by
    simp [globalMapA, sub_add_cancel]
  have e3 : globalMapA g s (i + 1) = g (s i) (s (i + 1)) (s (i + 1 + 1)) := by
    simp [globalMapA, add_sub_cancel_right]
  show g (globalMapA g s (i - 1)) (globalMapA g s i) (globalMapA g s (i + 1)) = s i
  rw [e1, e3]
  exact h _ _ _ _ _

/-- Over a subsingleton alphabet every rule is (trivially) a single coordinate followed
by a permutation. -/
theorem singleCoordinatePermA_of_subsingleton [Subsingleton A] (g : A → A → A → A) :
    SingleCoordinatePermA g := by
  refine ⟨Equiv.refl A, Or.inl ?_⟩
  funext a b c
  exact Subsingleton.elim _ _

/-! ## Alphabets with at least three letters: the claim always fails -/

variable [DecidableEq A]

-- [dropped: platform already declares twistRule]
variable {x₀ x₁ x₂ : A}

/-- The transposition fixes the marker letter `x₀`. -/
theorem swap_fix (h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂) : Equiv.swap x₁ x₂ x₀ = x₀ :=
  Equiv.swap_apply_of_ne_of_ne h₁ h₂

/-- Being equal to the marker letter is invariant under the transposition. -/
theorem swap_eq_marker_iff (h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂) (y : A) :
    Equiv.swap x₁ x₂ y = x₀ ↔ y = x₀ := by
  constructor
  · intro h
    have : Equiv.swap x₁ x₂ y = Equiv.swap x₁ x₂ x₀ := by rw [h, swap_fix h₁ h₂]
    exact (Equiv.swap x₁ x₂).injective this
  · rintro rfl
    exact swap_fix h₁ h₂

/-- **Self-decoding.** The conditional transposition inverts itself. -/
theorem twistRule_selfDecoder (h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂) :
    ∀ v w x y z, twistRule x₀ x₁ x₂ (twistRule x₀ x₁ x₂ v w x) (twistRule x₀ x₁ x₂ w x y)
      (twistRule x₀ x₁ x₂ x y z) = x := by
  intro v w x y z
  show (if (if z = x₀ then Equiv.swap x₁ x₂ y else y) = x₀
      then Equiv.swap x₁ x₂ (if y = x₀ then Equiv.swap x₁ x₂ x else x)
      else (if y = x₀ then Equiv.swap x₁ x₂ x else x)) = x
  by_cases hy : y = x₀
  · have hcond : (if z = x₀ then Equiv.swap x₁ x₂ y else y) = x₀ := by
      subst hy; split <;> simp [swap_fix h₁ h₂]
    rw [hcond, if_pos rfl, if_pos hy, Equiv.swap_apply_self]
  · have hcond : ¬ (if z = x₀ then Equiv.swap x₁ x₂ y else y) = x₀ := by
      split
      · rw [swap_eq_marker_iff h₁ h₂]; exact hy
      · exact hy
    rw [if_neg hcond, if_neg hy]

/-- The conditional transposition is an involution on every finite cycle. -/
theorem twistRule_involution (h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂) {n : ℕ} (s : ZMod n → A) :
    globalMapA (twistRule x₀ x₁ x₂) (globalMapA (twistRule x₀ x₁ x₂) s) = s :=
  globalMapA_involutive (twistRule_selfDecoder h₁ h₂) s

/-- Hence it is bijective on every nonempty finite cycle. -/
theorem twistRule_cycleBijectiveA [Fintype A] (h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂) :
    CycleBijectiveA (twistRule x₀ x₁ x₂) :=
  cycleBijectiveA_of_decoder3 _ _ (twistRule_selfDecoder h₁ h₂)

/-- The conditional transposition uses its middle cell. -/
theorem twistRule_dependsMiddle (h₁₂ : x₁ ≠ x₂) : DependsMiddleA (twistRule x₀ x₁ x₂) := by
  refine ⟨x₀, x₁, x₂, x₀, ?_⟩
  show (if x₀ = x₀ then Equiv.swap x₁ x₂ x₁ else x₁)
      ≠ (if x₀ = x₀ then Equiv.swap x₁ x₂ x₂ else x₂)
  rw [if_pos rfl, if_pos rfl, Equiv.swap_apply_left, Equiv.swap_apply_right]
  exact h₁₂.symm

/-- The conditional transposition uses its right cell. -/
theorem twistRule_dependsRight (h₁ : x₀ ≠ x₁) (h₁₂ : x₁ ≠ x₂) :
    DependsRightA (twistRule x₀ x₁ x₂) := by
  refine ⟨x₀, x₁, x₀, x₁, ?_⟩
  show (if x₀ = x₀ then Equiv.swap x₁ x₂ x₁ else x₁) ≠ (if x₁ = x₀ then Equiv.swap x₁ x₂ x₁ else x₁)
  rw [if_pos rfl, if_neg (Ne.symm h₁), Equiv.swap_apply_left]
  exact h₁₂.symm

/-- **The claim fails over every alphabet with at least three letters.** -/
theorem claim_fails_of_three_elements [Fintype A] (h₁ : x₀ ≠ x₁) (h₂ : x₀ ≠ x₂)
    (h₁₂ : x₁ ≠ x₂) :
    ¬ (∀ g : A → A → A → A, CycleBijectiveA g → SingleCoordinatePermA g) := by
  intro hall
  exact not_singleCoordinatePermA_of_MR (twistRule_dependsMiddle h₁₂)
    (twistRule_dependsRight h₁ h₁₂)
    (hall _ (twistRule_cycleBijectiveA h₁ h₂))

/-! ## The binary alphabet: the claim is true -/

-- [dropped: platform already declares BijUpTo4]
-- [dropped: platform already declares decidableBijUpTo4]
set_option maxRecDepth 100000 in
/-- **Exhaustive verification over the 256 binary rules**: bijectivity on the cycles of
length `1, 2, 3, 4` already forces the single-coordinate form.  (Length `≤ 3` does not:
twenty binary rules pass that weaker test.) -/
theorem binary_bijUpTo4_classification :
    ∀ g : Fin 2 → Fin 2 → Fin 2 → Fin 2, BijUpTo4 g → SingleCoordinatePermA g := by
  decide

/-- **Binary classification.** Over the binary alphabet the claim under test is true. -/
theorem binary_classification (g : Fin 2 → Fin 2 → Fin 2 → Fin 2) (hg : CycleBijectiveA g) :
    SingleCoordinatePermA g :=
  binary_bijUpTo4_classification g
    ⟨hg 1 one_pos, hg 2 (by norm_num), hg 3 (by norm_num), hg 4 (by norm_num)⟩

/-! ## The dichotomy -/

/-- **The size-two dichotomy.** For the alphabet `Fin q`, every rule that is bijective on
all nonempty finite cycles is a single coordinate followed by a permutation **iff**
`q ≤ 2`.  Radius-one reversibility is rigid exactly up to two letters. -/
theorem singleCoordinate_classification_iff (q : ℕ) :
    (∀ g : Fin q → Fin q → Fin q → Fin q, CycleBijectiveA g → SingleCoordinatePermA g)
      ↔ q ≤ 2 := by
  constructor
  · intro hall
    by_contra hq
    push_neg at hq
    have h0 : (0 : ℕ) < q := by omega
    have h1 : (1 : ℕ) < q := by omega
    have h2 : (2 : ℕ) < q := by omega
    exact claim_fails_of_three_elements (x₀ := (⟨0, h0⟩ : Fin q)) (x₁ := ⟨1, h1⟩) (x₂ := ⟨2, h2⟩)
      (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) (by simp [Fin.ext_iff]) hall
  · intro hq g _
    interval_cases q
    · exact singleCoordinatePermA_of_subsingleton g
    · exact singleCoordinatePermA_of_subsingleton g
    · exact binary_classification g ‹_›

end TernaryReversible
end Cryptography
section
open Cryptography
open TernaryReversible
variable {A : Type}
variable [DecidableEq A]
variable {x₀ x₁ x₂ : A}

theorem solution (q : ℕ) :
    (∀ g : Fin q → Fin q → Fin q → Fin q, CycleBijectiveA g → SingleCoordinatePermA g)
      ↔ q ≤ 2 :=
  Cryptography.TernaryReversible.singleCoordinate_classification_iff q

end
