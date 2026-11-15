-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.weightedAPCount_of_denseAPCount
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:36:11.784221+00:00
-- url     : https://prove2.me/submissions/51cdf82e-ba86-437b-85bb-a09f11b1ef10

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Szemeredi_Weighted
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Weighted arithmetic-progression counts

The transference argument is most naturally stated as a lower bound for a
normalized weighted count of progressions in `ZMod N`.  This file defines
that count and proves its elementary positivity and monotonicity properties.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators













theorem cyclicAPProduct_smul
    (k N : ℕ) (c : ℝ) (f : ZMod N → ℝ)
    (a d : ZMod N) :
    cyclicAPProduct k N (fun x => c * f x) a d =
      c ^ k * cyclicAPProduct k N f a d := by
  simp [cyclicAPProduct, Finset.prod_mul_distrib]



theorem cyclicAPCount_smul
    (k N : ℕ) [NeZero N] (c : ℝ) (f : ZMod N → ℝ) :
    cyclicAPCount k N (fun x => c * f x) =
      c ^ k * cyclicAPCount k N f := by
  simp_rw [cyclicAPCount, mean₂, cyclicAPProduct_smul, mean_smul]

theorem cyclicAPProduct_mono {k N : ℕ} {f g : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x)
    (a d : ZMod N) :
    cyclicAPProduct k N f a d ≤ cyclicAPProduct k N g a d := by
  exact Finset.prod_le_prod
    (fun j _ => hf (cyclicAPTerm a d j))
    (fun j _ => hfg (cyclicAPTerm a d j))

theorem cyclicAPCount_mono {k N : ℕ} [NeZero N]
    {f g : ZMod N → ℝ}
    (hf : ∀ x, 0 ≤ f x) (hfg : ∀ x, f x ≤ g x) :
    cyclicAPCount k N f ≤ cyclicAPCount k N g := by
  apply mean_mono
  intro a
  apply mean_mono
  intro d
  exact cyclicAPProduct_mono hf hfg a d

end Wikipedia.SzemeredisTheorem

end
/-!
# From dense sets to bounded dense weights

The hypergraph-removal layer will first produce a quantitative progression
count for dense finite sets.  This file proves the standard thresholding
step that upgrades such a theorem to functions `g : ZMod N → [0,1]`.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
/-- Thresholding at `δ/2` turns a dense bounded weight into a dense set.
The progression count loses the expected factor `(δ/2)^k`. -/
theorem solution
    {k N : ℕ} [NeZero N] {δ c : ℝ}
    (hδ0 : 0 ≤ δ)
    (hdense : HasDenseAPCount k N (δ / 2) c)
    {g : ZMod N → ℝ}
    (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∀ x, g x ≤ 1)
    (hmean : δ ≤ mean g) :
    (δ / 2) ^ k * c ≤ cyclicAPCount k N g := by
  let A : Finset (ZMod N) :=
    Finset.univ.filter fun x => δ / 2 ≤ g x
  have hpoint :
      ∀ x : ZMod N,
        g x ≤ δ / 2 + finsetIndicator A x := by
    intro x
    by_cases hx : x ∈ A
    · rw [finsetIndicator_of_mem hx]
      linarith [hg1 x]
    · rw [finsetIndicator_of_not_mem hx, add_zero]
      have hnot : ¬δ / 2 ≤ g x := by
        simpa [A] using hx
      exact le_of_lt (lt_of_not_ge hnot)
  have hmean_upper :=
    mean_mono (f := g)
      (g := fun x => δ / 2 + finsetIndicator A x) hpoint
  rw [mean_add, mean_const] at hmean_upper
  have hAmean : δ / 2 ≤ mean (finsetIndicator A) := by
    linarith
  have hsetCount := hdense A hAmean
  have hscaled_nonneg :
      ∀ x : ZMod N,
        0 ≤ δ / 2 * finsetIndicator A x := by
    intro x
    exact mul_nonneg (div_nonneg hδ0 (by norm_num))
      (by
        unfold finsetIndicator
        split <;> norm_num)
  have hscaled_le :
      ∀ x : ZMod N,
        δ / 2 * finsetIndicator A x ≤ g x := by
    intro x
    by_cases hx : x ∈ A
    · rw [finsetIndicator_of_mem hx, mul_one]
      simpa [A] using (Finset.mem_filter.mp hx).2
    · rw [finsetIndicator_of_not_mem hx, mul_zero]
      exact hg0 x
  have hcountMono :
      cyclicAPCount k N
          (fun x => δ / 2 * finsetIndicator A x) ≤
        cyclicAPCount k N g :=
    cyclicAPCount_mono (k := k) (N := N)
      hscaled_nonneg hscaled_le
  rw [cyclicAPCount_smul] at hcountMono
  calc
    (δ / 2) ^ k * c ≤
        (δ / 2) ^ k *
          cyclicAPCount k N (finsetIndicator A) :=
      mul_le_mul_of_nonneg_left hsetCount
        (pow_nonneg (div_nonneg hδ0 (by norm_num)) _)
    _ ≤ cyclicAPCount k N g := hcountMono
